#!/usr/bin/env bash
set -euo pipefail

lake build
lake build Mathlib.Util.AssertNoSorry
lake env lean Audit.lean
