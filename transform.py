import sys
from pathlib import Path
from dataclasses import dataclass, field
from typing import List, Optional, Tuple, Any

import tree_sitter_tlaplus as tstla
from tree_sitter import Language, Parser, Tree, Node as TSNode


# -----------------------------------------------------------------------------
# Parser setup
# -----------------------------------------------------------------------------

TLAPLUS_LANGUAGE = Language(tstla.language())
parser = Parser(TLAPLUS_LANGUAGE)

# -----------------------------------------------------------------------------
# Core data model: MyNode / MyTree + builders
# -----------------------------------------------------------------------------


@dataclass
class MyNode:
  # Core TS node attributes
  type: str
  start_byte: int
  end_byte: int
  start_point: Tuple[int, int]
  end_point: Tuple[int, int]
  is_named: bool
  is_missing: bool
  has_error: bool

  # Convenience
  text: str

  # Tree structure
  children: List["MyNode"] = field(default_factory=list)
  parent: Optional["MyNode"] = field(default=None, repr=False)

  @property
  def child_count(self) -> int:
    return len(self.children)

  @property
  def byte_range(self) -> Tuple[int, int]:
    return (self.start_byte, self.end_byte)

  def __str__(self) -> str:
    return f"{self.type} [{self.start_point} - {self.end_point}]"


@dataclass
class MyTree:
  root: MyNode
  language: Any = None
  source: Optional[str] = None


def build_my_node(ts_node: "TSNode", src_bytes: bytes, parent: Optional[MyNode] = None) -> MyNode:
  text = src_bytes[ts_node.start_byte: ts_node.end_byte].decode(
      "utf-8", errors="replace"
  )

  my = MyNode(
      type=ts_node.type,
      start_byte=ts_node.start_byte,
      end_byte=ts_node.end_byte,
      start_point=(ts_node.start_point.row, ts_node.start_point.column),
      end_point=(ts_node.end_point.row, ts_node.end_point.column),
      is_named=ts_node.is_named,
      is_missing=ts_node.is_missing,
      has_error=ts_node.has_error,
      text=text,
      children=[],
      parent=parent,
  )

  my.children = [
      build_my_node(child, src_bytes, parent=my) for child in ts_node.children
  ]

  return my


def build_my_tree(ts_tree: "Tree", src_bytes: bytes) -> MyTree:
  root = build_my_node(ts_tree.root_node, src_bytes, parent=None)
  lang = getattr(ts_tree, "language", None)
  src = src_bytes.decode("utf-8", errors="replace")
  return MyTree(root=root, language=lang, source=src)

# -----------------------------------------------------------------------------
# Generic helpers: traversal + text edits
# -----------------------------------------------------------------------------


def collect_nodes(root: MyNode, type_name: str) -> list[MyNode]:
  """
  Collect all nodes in the subtree rooted at `root` whose `type` equals `type_name`.
  """
  out: list[MyNode] = []

  def walk(node: MyNode):
    if node.type == type_name:
      out.append(node)
    for ch in node.children:
      walk(ch)

  walk(root)
  return out


def apply_edits(src: str, edits: list[tuple[int, int, str]]) -> str:
  # edits: list of (start, end, replacement) with arbitrary order
  edits = sorted(edits, key=lambda e: e[0], reverse=True)
  for start, end, repl in edits:
    src = src[:start] + repl + src[end:]
  return src

# -----------------------------------------------------------------------------
# PlusCal helpers: var decls, base vars, expr rewriting, assigns
# -----------------------------------------------------------------------------


def extract_name_and_init(decl: MyNode, src: str) -> tuple[str, str]:
  """
  From a pcal_var_decl node, return (name, init_suffix_text).

  Example: for 'y = 0':
      name = 'y'
      init = ' = 0'

  For 'mem \\in [a: Int, b: Int]':
      name = 'mem'
      init = ' \\in [a: Int, b: Int]'
  """
  id_node = None
  for child in decl.children:
    if child.type == "identifier":
      id_node = child
      break
  if id_node is None:
    raise ValueError(f"pcal_var_decl without top-level identifier: {decl}")

  name = id_node.text.strip()
  # includes leading space and the rest
  init = src[id_node.end_byte: decl.end_byte]
  return name, init


def collect_base_vars(root: MyNode) -> set[str]:
  """
  Collect the *base* variable names defined by pcal_var_decl nodes.
  """

  bases: set[str] = set()

  for decl in collect_nodes(root, "pcal_var_decl"):
    ident = None
    for ch in decl.children:
      if ch.type == "identifier":
        ident = ch.text.strip()
        break
    if not ident:
      continue
    if ident.endswith("1") or ident.endswith("2"):
      bases.add(ident[:-1])
    else:
      bases.add(ident)

  return bases


def rewrite_expr_with_suffix(
    expr_node: MyNode, src: str, base_vars: set[str], suffix: str
) -> str:
  """
  Return the text of expr_node, but with every identifier_ref whose text is
  in base_vars rewritten as name<suffix>.
  """
  id_nodes = collect_nodes(expr_node, "identifier_ref")
  id_nodes = [n for n in id_nodes if n.text.strip() in base_vars]

  if not id_nodes:
    return src[expr_node.start_byte: expr_node.end_byte]

  id_nodes.sort(key=lambda n: n.start_byte)

  pieces: list[str] = []
  last = expr_node.start_byte

  for n in id_nodes:
    start, end = n.start_byte, n.end_byte
    name = n.text.strip()

    pieces.append(src[last:start])
    pieces.append(name + suffix)
    last = end

  pieces.append(src[last: expr_node.end_byte])
  return "".join(pieces)


def get_bound_op_name_and_args(expr_node: MyNode) -> Optional[tuple[str, list[MyNode]]]:
  """
  If expr_node is a bound_op of the form
      Lap(arg1, arg2)
    or
      Exp(arg1, arg2, arg3)
  return (op_name, [arg1_node, arg2_node, ...]).
  Otherwise return None.
  """
  if expr_node.type != "bound_op":
    return None

  children = expr_node.children

  # First identifier_ref is the operator name
  op_ident = None
  for ch in children:
    if ch.type == "identifier_ref":
      op_ident = ch
      break
  if op_ident is None:
    return None

  op_name = op_ident.text.strip()

  # Arguments are between '(' and ')', skipping commas
  open_idx = next((i for i, c in enumerate(children) if c.type == "("), None)
  close_idx = None
  for i in range(len(children) - 1, -1, -1):
    if children[i].type == ")":
      close_idx = i
      break

  if open_idx is None or close_idx is None or close_idx <= open_idx:
    return None

  arg_children = children[open_idx + 1: close_idx]
  args = [c for c in arg_children if c.type != ","]

  return op_name, args


def get_lhs_and_assign(assign_node: MyNode) -> tuple[MyNode, MyNode, str]:
  """
  From a pcal_assign, find:
    - lhs identifier_ref node
    - assign token node (the ':=')
    - lhs name text
  """
  lhs_node = None
  assign_tok = None

  for ch in assign_node.children:
    if ch.type == "pcal_lhs":
      lhs_node = ch
    elif ch.type == "assign":
      assign_tok = ch

  if lhs_node is None or assign_tok is None:
    raise ValueError("pcal_assign missing lhs or assign")

  ident_ref = None
  for ch in lhs_node.children:
    if ch.type == "identifier_ref":
      ident_ref = ch
      break
  if ident_ref is None:
    raise ValueError("pcal_lhs without identifier_ref")

  return ident_ref, assign_tok, ident_ref.text.strip()


def get_rhs_expr(assign_node: MyNode) -> MyNode:
  """
  The RHS is the child that is not pcal_lhs or assign.
  """
  for ch in assign_node.children:
    if ch.type not in ("pcal_lhs", "assign"):
      return ch
  raise ValueError("pcal_assign without RHS expression")


def get_if_condition_node(if_node: MyNode) -> MyNode:
  """
  Return the node representing the condition in a pcal_if.
  """
  for ch in if_node.children:
    if ch.type not in ("if", "(", ")", "pcal_algorithm_body", "else"):
      return ch
  raise ValueError("pcal_if without a recognizable condition")


def get_while_condition_node(while_node: MyNode) -> MyNode:
  """
  Return the node representing the condition in a pcal_while.
  """
  for ch in while_node.children:
    if ch.type not in ("while", "(", ")", "pcal_algorithm_body"):
      return ch
  raise ValueError("pcal_while without a recognizable condition")

# -----------------------------------------------------------------------------
# Transforms
# -----------------------------------------------------------------------------


def build_pcal_var_decls_text(block: MyNode, src: str) -> str:
  """
  Rebuilds a PlusCal 'variables' block so that each original decl v becomes:

      v1 <init>, v2 <init>,

  Then appends:
      (* Privacy cost variables *)
      v_eps = 0,
      v_delta = 0;

  Comments and indentation are preserved.
  """
  # Indent for 'variables' keyword
  var_indent = " " * block.start_point[1]

  # Indent for declarations (based on first pcal_var_decl)
  first_decl = None
  for child in block.children:
    if child.type == "pcal_var_decl":
      first_decl = child
      break
  decl_indent = " " * (
      first_decl.start_point[1] if first_decl else (block.start_point[1] + 2)
  )

  lines: list[str] = []
  lines.append(f"{var_indent}variables")

  for child in block.children:
    if child.type == "block_comment":
      lines.append(f"{decl_indent}{child.text}")
    elif child.type == "pcal_var_decl":
      name, init = extract_name_and_init(child, src)
      line = f"{decl_indent}{name}1{init}, {name}2{init},"
      lines.append(line)
    else:
      continue

  lines.append(f"{decl_indent}(* Privacy cost variables *)")
  lines.append(f"{decl_indent}v_eps = 0,")
  lines.append(f"{decl_indent}v_delta = 0,")

  last = lines[-1]
  if last.rstrip().endswith(","):
    idx = last.rfind(",")
    lines[-1] = last[:idx] + ";" + last[idx + 1:]

  return "\n".join(lines)


def transform_pcal_var_decls_and_reparse(my_tree: MyTree) -> MyTree:
  """
  Transform all PlusCal variable declaration blocks.

  For each 'pcal_var_decls' block:
    • Every variable declaration 'v <init>' becomes:
          v1 <init>, v2 <init>,
    • A new comment and two fresh variables are appended:
          (* Privacy cost variables *)
          v_eps = 0,
          v_delta = 0;
  """
  assert my_tree.source is not None
  src = my_tree.source

  blocks = collect_nodes(my_tree.root, "pcal_var_decls")

  edits: list[tuple[int, int, str]] = []
  for block in blocks:
    new_text = build_pcal_var_decls_text(block, src)
    edits.append((block.start_byte, block.end_byte, new_text))

  if not edits:
    return my_tree

  src = apply_edits(src, edits)

  new_bytes = src.encode("utf-8")
  new_ts_tree = parser.parse(new_bytes)
  return build_my_tree(new_ts_tree, new_bytes)


def transform_pcal_assigns_and_reparse(my_tree: MyTree, base_vars: set[str]) -> MyTree:
  """
  Transform all PlusCal assignments.

  For each 'pcal_assign':
    • Generic case:  v := expr
          becomes
          v1 := expr¹ || v2 := expr²
      where occurrences of declared variables inside expr are rewritten to
      their '1' or '2' counterparts.

    • Special Lap case:  v := Lap(eps, expr)
          becomes
          with (res ∈ AbsLap(eps, expr¹, expr², v_eps, v_delta)) {
            v1 := res[1] || v2 := res[2] || v_eps := res[3] || v_delta := res[4]
          }

    • Special Exp case:  v := Exp(eps, score, expr)
          becomes
          with (res ∈ AbsExp(eps, score¹, expr¹, score², expr², v_eps, v_delta)) {
            v1 := res[1] || v2 := res[2] || v_eps := res[3] || v_delta := res[4]
          }
  """

  assert my_tree.source is not None
  src = my_tree.source

  base_vars = collect_base_vars(my_tree.root)
  assigns = collect_nodes(my_tree.root, "pcal_assign")

  edits: list[tuple[int, int, str]] = []

  for assign in assigns:
    rhs = get_rhs_expr(assign)

    # Try to see if RHS is Lap(...) or Exp(...)
    bound_info = get_bound_op_name_and_args(rhs)
    op_name: Optional[str] = None
    arg_nodes: list[MyNode] = []
    if bound_info is not None:
      op_name, arg_nodes = bound_info

    # LHS parts
    lhs_ident_node, assign_tok, lhs_name = get_lhs_and_assign(assign)

    # Everything before the identifier (indent + optional label)
    prefix = src[assign.start_byte:lhs_ident_node.start_byte]
    # Everything between the identifier and ':=' (e.g. '[1]', spaces)
    lhs_tail = src[lhs_ident_node.end_byte:assign_tok.start_byte]

    # Find where the line starts and where the LHS identifier starts
    line_start = src.rfind("\n", 0, assign.start_byte) + 1
    line_prefix = src[line_start: assign.start_byte]
    prefix_len = len(line_prefix)

    # 'with' will sit after the existing line_prefix
    with_indent = ""
    body_indent = " " * (prefix_len + 2)    # a bit deeper than the 'with'
    close_indent = " " * prefix_len         # align '}' under 'with'

    # ------------------------------------------------------------------
    # Special case 1: Lap(eps, expr)
    #    var := Lap(earg, expr)
    # => with (res \in AbsLap(earg, expr1, expr2, v_eps, v_delta)) {
    #        var1 := res[1] || var2 := res[2] || v_eps := res[3] || v_delta := res[4]
    #    }
    # ------------------------------------------------------------------
    if op_name == "Lap" and len(arg_nodes) == 2:
      earg_node, expr_node = arg_nodes

      earg_text = src[earg_node.start_byte:earg_node.end_byte]
      expr1 = rewrite_expr_with_suffix(expr_node, src, base_vars, "1")
      expr2 = rewrite_expr_with_suffix(expr_node, src, base_vars, "2")

      line1 = (
          f"{with_indent}with (res \\in AbsLap("
          f"{earg_text}, {expr1}, {expr2}, v_eps, v_delta)) {{"
      )
      line2 = (
          f"{body_indent}{lhs_name}1 := res[1] || {lhs_name}2 := res[2] "
          f"|| v_eps := res[3] || v_delta := res[4]"
      )
      line3 = f"{close_indent}}}"

      replacement = "\n".join([line1, line2, line3])

    # ------------------------------------------------------------------
    # Special case 2: Exp(eps, score, expr)
    #    var := Exp(earg, score, expr)
    # => with (res \in AbsExp(earg, score1, expr1, score2, expr2, v_eps, v_delta)) {
    #        var1 := res[1] || var2 := res[2] || v_eps := res[3] || v_delta := res[4]
    #    }
    # ------------------------------------------------------------------
    elif op_name == "Exp" and len(arg_nodes) == 3:
      earg_node, score_node, expr_node = arg_nodes

      earg_text = src[earg_node.start_byte:earg_node.end_byte]

      score1 = rewrite_expr_with_suffix(score_node, src, base_vars, "1")
      expr1 = rewrite_expr_with_suffix(expr_node,  src, base_vars, "1")
      score2 = rewrite_expr_with_suffix(score_node, src, base_vars, "2")
      expr2 = rewrite_expr_with_suffix(expr_node,  src, base_vars, "2")

      line1 = (
          f"{with_indent}with (res \\in AbsExp("
          f"{earg_text}, {score1}, {expr1}, {score2}, {expr2}, v_eps, v_delta)) {{"
      )
      line2 = (
          f"{body_indent}{lhs_name}1 := res[1] || {lhs_name}2 := res[2] "
          f"|| v_eps := res[3] || v_delta := res[4]"
      )
      line3 = f"{close_indent}}}"

      replacement = "\n".join([line1, line2, line3])

    # ------------------------------------------------------------------
    # Generic case: var[...] := expr
    # ------------------------------------------------------------------
    else:
      lhs1 = lhs_name + "1"
      lhs2 = lhs_name + "2"

      expr1 = rewrite_expr_with_suffix(rhs, src, base_vars, "1")
      expr2 = rewrite_expr_with_suffix(rhs, src, base_vars, "2")

      # preserve lhs_tail (e.g. '[1]')
      replacement = (
          f"{prefix}{lhs1}{lhs_tail}:= {expr1} || "
          f"{lhs2}{lhs_tail}:= {expr2}"
      )

    edits.append((assign.start_byte, assign.end_byte, replacement))

  if not edits:
    return my_tree  # nothing to do

  src = apply_edits(src, edits)

  new_bytes = src.encode("utf-8")
  new_ts_tree = parser.parse(new_bytes)
  return build_my_tree(new_ts_tree, new_bytes)


def transform_pcal_ifs_and_reparse(my_tree: MyTree, base_vars: set[str]) -> MyTree:
  """
  Transform all PlusCal 'if' statements.

  Each:
      if (Cond) { ... } else { ... }

  becomes:
      await ((Cond¹) = (Cond²)); if (Cond¹) { ... } else { ... }

  • Cond¹ and Cond² are produced by rewriting identifier references inside
    Cond to their '1' and '2' variants.
  • Only the condition expression is replaced; the then/else bodies are
    preserved and will be transformed by later passes (assignments, whiles)
  """

  assert my_tree.source is not None
  src = my_tree.source

  base_vars = collect_base_vars(my_tree.root)
  ifs = collect_nodes(my_tree.root, "pcal_if")

  edits: list[tuple[int, int, str]] = []

  for if_node in ifs:
    cond_node = get_if_condition_node(if_node)

    # Cond1 / Cond2 by suffixing identifier_refs inside the condition
    cond1 = rewrite_expr_with_suffix(cond_node, src, base_vars, "1")
    cond2 = rewrite_expr_with_suffix(cond_node, src, base_vars, "2")

    # (1) replace the condition text itself with cond1
    edits.append((cond_node.start_byte, cond_node.end_byte, cond1))

    # (2) insert await before the 'if' keyword
    await_code = f"await (({cond1}) = ({cond2})); "
    edits.append((if_node.start_byte, if_node.start_byte, await_code))

  if not edits:
    return my_tree

  src = apply_edits(src, edits)  # your reverse-sorted apply

  new_bytes = src.encode("utf-8")
  new_ts_tree = parser.parse(new_bytes)
  return build_my_tree(new_ts_tree, new_bytes)


def transform_pcal_whiles_and_reparse(my_tree: MyTree, base_vars: set[str]) -> MyTree:
  """
  Transform all PlusCal 'while' statements.

  Each:
      while (Cond) { ... };

  becomes:
      while (Cond¹) { await ((Cond¹) = (Cond²));
        ...
      }; await ((Cond¹) = (Cond²));

  • Cond¹ and Cond² are constructed by rewriting variable references inside
    Cond to their '1' and '2' forms.
  • The body will be transformed by later passes.
  """

  assert my_tree.source is not None
  src = my_tree.source

  base_vars = collect_base_vars(my_tree.root)
  whiles = collect_nodes(my_tree.root, "pcal_while")

  edits: list[tuple[int, int, str]] = []

  for w in whiles:
    cond_node = get_while_condition_node(w)

    # Original condition text
    cond_src = src[cond_node.start_byte:cond_node.end_byte]

    # Cond1 / Cond2 by suffixing identifier_refs
    cond1 = rewrite_expr_with_suffix(cond_node, src, base_vars, "1")
    cond2 = rewrite_expr_with_suffix(cond_node, src, base_vars, "2")

    # --- (1) replace condition: Cond -> Cond1 ---
    edits.append((cond_node.start_byte, cond_node.end_byte, cond1))

    # --- (2) insert inner await right after the '{' of the body ---
    body_node = None
    for ch in w.children:
      if ch.type == "pcal_algorithm_body":
        body_node = ch
        break

    body_text = src[body_node.start_byte:body_node.end_byte]  # e.g. "{ ... }"
    brace_rel = body_text.find("{")
    if brace_rel != -1:
      insert_pos = body_node.start_byte + brace_rel + 1  # just after '{'
      inner_await = f" await (({cond1}) = ({cond2}));"
      edits.append((insert_pos, insert_pos, inner_await))

    # --- (3) insert trailing await after the while's semicolon ---
    semi_index = src.find(";", w.end_byte)
    if semi_index != -1:
      trailing_await = f" await (({cond1}) = ({cond2}));"
      insert_after_semi = semi_index + 1
      edits.append((insert_after_semi, insert_after_semi, trailing_await))

  if not edits:
    return my_tree

  src = apply_edits(src, edits)

  new_bytes = src.encode("utf-8")
  new_ts_tree = parser.parse(new_bytes)
  return build_my_tree(new_ts_tree, new_bytes)


def rewrite_module_name(src: str, old_name: str, new_name: str) -> str:
  """
  Replace the MODULE header name.
  """
  return src.replace(f"MODULE {old_name}", f"MODULE {new_name}", 1)

# -----------------------------------------------------------------------------
# Debug / printing
# -----------------------------------------------------------------------------


def print_my_node(node: MyNode, indent: str = ""):
  print(f"{indent}{node}")

  txt = node.text
  if txt and txt.strip():
    one_line = " ".join(line.strip() for line in txt.splitlines())
    if len(one_line) > 200:
      one_line = one_line[:197] + "..."
    print(f"{indent}  text: {one_line}")

  for child in node.children:
    print_my_node(child, indent + "  ")

# -----------------------------------------------------------------------------
# CLI
# -----------------------------------------------------------------------------


def main():
  args = sys.argv[1:]
  show_tree = "--tree" in args
  paths = [a for a in args if not a.startswith("--")]

  if len(paths) < 1:
    print("Usage: python print_tla_nodes.py [--tree] path/to/spec.tla")
    sys.exit(2)

  path = Path(paths[0])
  if not path.exists():
    print("File not found:", path)
    sys.exit(1)

  src_bytes = path.read_bytes()
  ts_tree = parser.parse(src_bytes)
  my_tree = build_my_tree(ts_tree, src_bytes)

  # 1) duplicate variables and add v_eps/v_delta
  my_tree = transform_pcal_var_decls_and_reparse(my_tree)

  # Collect base_vars
  base_vars = collect_base_vars(my_tree.root)

  # 2) transform ifs: await(cond1 = cond2); if (cond1) { ... } else { ... }
  my_tree = transform_pcal_ifs_and_reparse(my_tree, base_vars)

  # 3) transform whiles: await ((cond1) = (cond2)); while (cond1) { ...; await ((cond1) = (cond2)); }
  my_tree = transform_pcal_whiles_and_reparse(my_tree, base_vars)

  # 4) split assignments (and Lap/Exp to AbsLap/AbsExp)
  my_tree = transform_pcal_assigns_and_reparse(my_tree, base_vars)

  # Extract old module name from file name
  old_name = path.stem
  new_name = old_name + "_transf"

  # Update module header text
  updated_src = rewrite_module_name(my_tree.source, old_name, new_name)

  # Reparse so tree is correct (OPTIONAL but recommended)
  new_bytes = updated_src.encode("utf-8")
  new_ts_tree = parser.parse(new_bytes)
  my_tree = build_my_tree(new_ts_tree, new_bytes)

  # Determine output path
  out_path = path.with_name(path.stem + "_transf.tla")

  # Write transformed source
  out_path.write_text(my_tree.source, encoding="utf-8")
  print(f"\nWrote transformed TLA+ file to: {out_path}")

  # Tree dump only when flag present
  if show_tree:
    print("\n=== Tree dump ===")
    print_my_node(my_tree.root)


if __name__ == "__main__":
  main()
