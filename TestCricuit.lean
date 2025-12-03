import QuantumInfo.Finite.Qubit.Basic
import QuantumInfo.Finite.CPTPMap

#eval
  let u1 := (Qubit.H * Qubit.H).val
  let u2 := (Qubit.X * Qubit.X).val
  decide (u1 0 0 = u2 0 0) && decide (u1 0 1 = u2 0 1) &&
  decide (u1 1 0 = u2 1 0) && decide (u1 1 1 = u2 1 1)
