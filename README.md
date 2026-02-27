# A5CosmicNecessity

**Uniqueness of Icosahedral Holonomy from Three Physical Principles
and Its Algebraic Consequences for Fundamental Constants**

Author: M. Numagaki (Independent Researcher, Kumamoto, Japan)
Date: February 2026


## Prerequisites

- [elan](https://github.com/leanprover/elan) ≥ 4.0.0

## Build

```bash
# 1. Clone or copy this directory
cd A5CosmicNecessity

# 2. Resolve dependencies and download Mathlib cache
lake update
lake exe cache get

# 3. Build
lake build
```

## Verification Target

- **sorry = 0**
- **axiom = 0**

## Toolchain

- Lean: `leanprover/lean4:v4.29.0-rc1`
- Mathlib: compatible version (resolved via `lake update`)
