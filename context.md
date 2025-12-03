## Overview

This file defines a very small “circuit language” for **single‑qubit circuits**, and a way to interpret such circuits as concrete unitaries on the qubit Hilbert space used in `Lean-QuantumInfo`. It then provides a **boolean** function that checks whether two circuits implement exactly the same 2×2 unitary matrix.

The key point: it **reuses** all the existing gate definitions (`Qubit.Z`, `Qubit.X`, etc.) and just adds syntax + evaluation on top.

---

## Imports

```lean
import QuantumInfo.Finite.Qubit.Basic
import QuantumInfo.Finite.CPTPMap  -- brings in 𝐔
```

- `Qubit.Basic` defines:
  - `abbrev Qubit := Fin 2`
  - single‑qubit unitaries `Qubit.Z`, `Qubit.X`, `Qubit.Y`, `Qubit.H`, `Qubit.S`, `Qubit.T` as elements of `𝐔[Qubit]`.
- `Finite.CPTPMap` brings in the notation `𝐔[α]` for the unitary group on a finite type `α`. So `𝐔[Qubit]` is the type of 2×2 unitary matrices acting on a qubit.

---

## 1. Gate syntax and circuit type

```lean
/-- Primitive single-qubit gates, as syntax. -/
inductive SingleQubitGate
  | Z | X | Y | H | S | T
deriving Repr, DecidableEq

/-- A single-qubit circuit is a list of gates applied in order (head first). -/
abbrev SingleQubitCircuit := List SingleQubitGate
```

- `SingleQubitGate` is an **inductive syntax type**: it doesn’t define any new math, it’s just a small alphabet for the standard qubit gates.
- `SingleQubitCircuit` is just `List SingleQubitGate`.
  - A value like `[.H, .T, .X]` represents “apply H, then T, then X” to a qubit state.

This keeps a clear separation between:

- **syntax** (`SingleQubitGate`, `SingleQubitCircuit`), and
- **semantics** (unitary matrices `𝐔[Qubit]`).

---

## 2. Interpreting gates as unitaries

```lean
namespace SingleQubitGate

/-- Interpret a primitive gate as the corresponding unitary 𝐔[Qubit]. -/
noncomputable def toUnitary : SingleQubitGate → 𝐔[Qubit]
  | .Z => Qubit.Z
  | .X => Qubit.X
  | .Y => Qubit.Y
  | .H => Qubit.H
  | .S => Qubit.S
  | .T => Qubit.T

end SingleQubitGate
```

- `toUnitary` is the **semantic map** from the syntactic gate constructors to the already-defined unitaries in `Qubit.Basic`.
- We don’t re‑implement any matrices; we just call the existing `Qubit.Z`, `Qubit.X`, etc.

So, for example:

- `SingleQubitGate.toUnitary SingleQubitGate.X = Qubit.X : 𝐔[Qubit]`.

---

## 3. Evaluating a circuit to a unitary

```lean
/-- Evaluate a circuit to a single unitary, left-to-right application. -/
noncomputable def evalCircuit (c : SingleQubitCircuit) : 𝐔[Qubit] :=
  c.foldl (fun U g => SingleQubitGate.toUnitary g * U) (1 : 𝐔[Qubit])
```

- `evalCircuit` turns a **list of gates** into a **single unitary** $U : 𝐔[Qubit]$.
- It uses `foldl` with:
  - accumulator `U : 𝐔[Qubit]`,
  - step `fun U g => SingleQubitGate.toUnitary g * U`,
  - initial value `1 : 𝐔[Qubit]` (the identity unitary).

Semantics:

- For a circuit `[g₁, g₂, …, gₙ]`, `evalCircuit` computes

$$
U = \text{toUnitary}(g_n) * \cdots * \text{toUnitary}(g_2) * \text{toUnitary}(g_1),
$$

so when this `U` acts on a state vector, the gates are applied **in list order**: `g₁` first, then `g₂`, …, then `gₙ`.

---

## 4. Boolean equality of circuits (matrix-level)

```lean
/-- Boolean check: do two circuits have exactly the same 2×2 unitary matrix? -/
noncomputable def circuitsEqBool (c₁ c₂ : SingleQubitCircuit) : Bool :=
  let U₁ := (evalCircuit c₁).val
  let U₂ := (evalCircuit c₂).val
  let e00 := decide (U₁ 0 0 = U₂ 0 0)
  let e01 := decide (U₁ 0 1 = U₂ 0 1)
  let e10 := decide (U₁ 1 0 = U₂ 1 0)
  let e11 := decide (U₁ 1 1 = U₂ 1 1)
  e00 && e01 && e10 && e11
```

- `(evalCircuit c).val` is the underlying `Matrix Qubit Qubit ℂ` for the unitary `evalCircuit c : 𝐔[Qubit]`.
- Since `Qubit = Fin 2`, the matrix has exactly 4 entries: indices `0,1`.
- For two circuits `c₁`, `c₂` we:
  - compute their unitaries: `U₁`, `U₂`,
  - compare each of the four complex entries for **exact equality**, using `decide (U₁ i j = U₂ i j) : Bool`,
  - return the conjunction of those four booleans.

So:

- `circuitsEqBool c₁ c₂ = true` exactly when the two 2×2 matrices are **identical** entrywise.
- This is a straight Bool-based check, suitable for e.g. testing or simple automation.
- It does **not** mod out by global phase; it checks literal equality of matrices.

---

## How this matches the original TODO

> Make a type in lean4 for a single qbit circuit (array of single qubit gate) \& outputs a boolean

- `SingleQubitGate` + `SingleQubitCircuit` give the types.
- `circuitsEqBool` is the boolean output comparing two circuits.

> Write a function in lean4 that takes in 2 circuits and computes the unitary matrix for those 2 circuits

- `evalCircuit : SingleQubitCircuit → 𝐔[Qubit]` computes the unitary for each circuit.
- Internally, `circuitsEqBool` uses `evalCircuit` on both inputs.

> check both of the matrix entry by entry … store that in a boolean, return the boolean value

- `circuitsEqBool` implements exactly that: it checks all 4 entries (0,0), (0,1), (1,0), (1,1) and returns the conjunction.

> (optional) explore the lean-quantum-info more to find more useful lemmas

- This code is designed to sit on top of the existing `Qubit` lemmas:
  - `Z_sq`, `X_sq`, `H_sq`, `S_sq`, `T_sq`, commutation / anticommutation lemmas, etc.
- You can now prove circuit equivalences using those lemmas, and if desired, connect them to `circuitsEqBool` for testing.
