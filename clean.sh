#!/bin/bash
cd examples
find . -maxdepth 2 -not -path '*/.*' -type d -name 'states' -exec rm -rf {} +
find . -maxdepth 2 -not -path '*/.*' -type f \( -name '*.out' -o -name '*.old' \) -delete
