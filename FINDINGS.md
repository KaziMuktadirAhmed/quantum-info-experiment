# FINDINGS: Lean quantum circuit equivalence proof tactics

## Overview

We compared two implementations for checking 2-qubit circuit equivalence:
- `experiment.lean` (per-entry Bool-based comparison)
- `2_qubit_circuit.lean` (whole-matrix equality with `norm_num`)

Both define the same domain model (`TwoQubitGate`, `TwoQubitCircuit`, `toUnitary`, `evalCircuit`), but use different proof styles and have different heartbeat characteristics.

---

## Key definitions

### `experiment.lean`
- `circuitsEqBool : TwoQubitCircuit → TwoQubitCircuit → Bool`
- compares all entries via:
  - `let U₁ := (evalCircuit c₁).val`
  - `let U₂ := (evalCircuit c₂).val`
  - `(basisStates.product basisStates).all fun (row, col) => decide (U₁ row col = U₂ row col)`
- Example lemma: `TwiceId : circuitsEqBool [.cnot, .cnot, .cnot] [.cnot] = true`

### `2_qubit_circuit.lean`
- `circuitsEq : TwoQubitCircuit → TwoQubitCircuit → Prop`
- compares matrices directly:
  - `(evalCircuit c₁).val = (evalCircuit c₂).val`
- lemmas: `cnotTwiceId`, `czTwice`
- proof uses `by ... norm_num [basisStates, List.all, List.product, Qubit.CNOT]`

---

## Heartbeat and diagnostics comparison

### `experiment.lean` output (core part)

1 proof goal after `unfold`:
- explicit conjunction of 16 equalities:
  - `(↑Qubit.CNOT * (↑Qubit.CNOT * ↑Qubit.CNOT)) (i, j) (k, l) = ↑Qubit.CNOT (i, j) (k, l)` for all four row/col pairs
- The goal is basically a large nested `and` tree.

Diagnostics revealed heavy reduction expansion:
- `+25k` unfolding for declarations such as `AddMonoid.toZero`, `Matrix`, `unitary`, `Zero.zero`, etc.
- `+29k` unfolding for instances (`AddZero.toZero`, `AddMonoid.toAddZeroClass`, `Ring.toSemiring`, etc.)
- `+34k` unfolded reducible declarations (`Subtype.val`, `Qubit`, `Matrix.unitaryGroup`, `TwoQubitGate.casesOn`, ...)
- `type_class` context includes dozens of entries for algebra structures.
- Main tactic chain:
  - `unfold ...` to expose matrix values
  - `simp [basisStates]`
  - `all_goals` with `simp [Matrix.mul_apply, Qubit.CNOT, Qubit.X]`
  - `simp [Fintype.sum_prod_type, Fin.sum_univ_succ]`

**Implication**: this is highly expensive due to per-entry symbolic expansion and repeated numeric evaluation over 16 equations.

### `2_qubit_circuit.lean` output (core part)

1 goal after `unfold circuitsEq`:
- one equality of two `List.foldl` expressions converting gate sequences to matrices.
- side condition `true = true` from lemma context.

Diagnostics are significantly lighter:
- `+5.8k` unfolded declarations (`OfNat.ofNat`, `AddMonoid.toZero`, `zero`, etc.)
- `+5.6k` instances unfolded (`AddZero.toZero`, `AddMonoid.toAddZeroClass`, etc.)
- `+593` reducible, including `Qubit`, `Matrix.unitaryGroup`, `Subtype.val`, `TwoQubitGate.casesOn`.
- `def_eq` and `kernel` also much smaller.

**Implication**: using global matrix equality removes per-element expansion and prevents the giant `and` tree, resulting in lower heartbeat consumption.

---

## Tactical difference and scalability analysis

### `experiment.lean`: Boolean entrywise technique

- Good as a direct mechanical check (matches classical expectation: compare entries).
- **Scalability concern**:
  - complexity grows as O(n^2) in matrix entries for n-qubit system.
  - each entry may involve nested sums in matrix multiplication, causing huge intermediate proof workload.
  - high risk of `heartbeats` timeout once circuits grow slightly bigger or gates are more complex.
- In practice this style is useful only for small fixed-size circuits and as a correctness brute-force.

### `2_qubit_circuit.lean`: Matrix-level equality with `norm_num`

- Leverages `norm_num` in a much smaller logical space: overall matrix value equation.
- `norm_num` performs arithmetic reduction at the matrix level; better search and fewer repeated reductions.
- Scale-wise still limited (matrix dimension still exponential with qubit count), but this pattern is more composable:
  - Could prove generic `evalCircuit` composition properties using unitary algebra, avoiding full unfold.
- Less sensitive to explicit `List.product` details; it can use `matrix.ext` or direct `Qubit.CNOT` symbolic identities.

### Comparative heartbeats

- `experiment.lean` is likely 5-10× heavier per lemma than `2_qubit_circuit.lean` in this case.
- Backend breakdown shows the worst cost is recurring `Matrix.mul_apply` over 16 entries.
- `2_qubit_circuit.lean` avoids this by keeping equations at matrix/unital values.

---

## Recommendations

1. Use `2_qubit_circuit.lean` style: `circuitsEq` matrix equality + `norm_num`.
2. Avoid explicit elementwise loops; use algebraic lemmas with `matrix.ext` and group theory style rewriting.
3. For larger circuits, avoid `basisStates.product basisStates` and prove `evalCircuit c₁ = evalCircuit c₂` by rewriting via circuit identities.
4. Keep `#check`/`#eval` limited and use `set_option diagnostics true` / `set_option maxHeartbeats` to profile.

---

## InfoViewer snippets

### `experiment.lean`

```lean
1 goal
⊢ ((((↑Qubit.CNOT * (↑Qubit.CNOT * ↑Qubit.CNOT)) (0, 0) (0, 0) = ↑Qubit.CNOT (0, 0) (0, 0) ∧
... (16 eqns) ...

[diag] Diagnostics ▼
  [reduction] unfolded declarations (max: 26509, num: 69): ...
  ...
```

### `2_qubit_circuit.lean`

```lean
1 goal
⊢ (↑(List.foldl ... ) = ↑(List.foldl ...)) = (true = true)
⊢ TwoQubitCircuit → ↥𝐔[Qubit × Qubit]

[diag] Diagnostics ▼
  [reduction] unfolded declarations (max: 5864, num: 19): ...
  ...
```
