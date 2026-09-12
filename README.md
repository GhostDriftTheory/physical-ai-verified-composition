# Physical AI Verified Composition

[![Lean verification](https://github.com/GhostDriftTheory/physical-ai-verified-composition/actions/workflows/lean.yml/badge.svg)](https://github.com/GhostDriftTheory/physical-ai-verified-composition/actions/workflows/lean.yml)

A standalone Lean 4 kernel formalizing information limits and conditional composition of local guarantees across finite sequences.

## What this formalizes

- information loss can prevent simultaneously sound and complete decisions;
- downstream processing cannot recover a distinction already erased upstream;
- local guarantees do not automatically compose;
- explicit abstract interface conditions support finite-length composition;
- progress requires assumptions separate from partial correctness.

## Main theorem names

- `information_loss_impossibility`
- `exact_decisions_iff_separation`
- `pipeline_information_loss_impossibility`
- `summary_transferable_iff_compatible`
- `arbitrary_length_composition`
- `all_prefixes_preserve_invariant`

## Verification

```bash
lean PhysicalAIPublicComposition.lean
```

Lean version: `4.33.1`  
Dependencies: Lean `Init` only. No Mathlib.  
GitHub Actions runs the same file-level verification on pushes to `main`, pull requests targeting `main`, and manual dispatch.

## Scope / interpretation boundary

This is an abstract mathematical kernel. It does not prove safety of a particular robot, device, deployment, or physical system, and it does not prescribe a unique implementation. Finite compositionality is not a claim of liveness, fairness, execution-time scalability, or deployment scalability. Finite progress does not establish fairness or eventual completion of arbitrary infinite executions. `ForwardSimulation` uses one-step matching; stuttering and multi-step matching are outside this kernel's scope.

Concrete engineering mechanisms are intentionally outside the scope of this public kernel.
