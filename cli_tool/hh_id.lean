-- Auto-generated from OpenQASM 3.0
import SingleQubitCircuit
open SingleQubitGate

namespace SingleQubitCircuit

def circuit1 : SingleQubitCircuit := [.H, .H]
def circuit2 : SingleQubitCircuit := []

lemma hh_id_eq :
  circuitsEqBool circuit1 circuit2 = true := by
  unfold circuitsEqBool evalCircuit SingleQubitGate.toUnitary
  simp [Qubit.H_sq, Qubit.X_sq]

end SingleQubitCircuit
