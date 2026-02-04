# QASM to Lean Proof Generator

Minimal CLI tool to convert OpenQASM 3.0 circuits to Lean 4 equivalence proofs.

## 🎯 Purpose

Parse single-qubit QASM circuits → Generate Lean code → Verify proofs.

## 🚀 Quick Start

### Prerequisites
```bash
# Pure Python 3 - NO dependencies!
# Lean 4 installed (for verification)
```

### Usage

```bash
# Generate Lean code only
python qasm_to_lean.py circuit1.qasm circuit2.qasm -l myProof -o proof.lean

# Generate + verify
python qasm_to_lean.py hh.qasm id.qasm -l hTwiceIsId --verify

# Verify in Lean project
python qasm_to_lean.py hh.qasm id.qasm --verify --lean-project ../
```

## 📖 Examples

### 1. H² = I
**hh.qasm**:
```qasm
OPENQASM 3;
include "stdgates.inc";
qubit q;
h q;
h q;
```

**id.qasm**:
```qasm
OPENQASM 3;
include "stdgates.inc";
qubit q;
```

```bash
python qasm_to_lean.py hh.qasm id.qasm -l hTwiceIsId --verify
```

**Generated Lean**:
```lean
def circuit1 : Circuit := [.H, .H]
def circuit2 : Circuit := []
lemma hTwiceIsId : circuitsEq circuit1 circuit2 = true := by
  unfold circuitsEq evalCircuit Gate.toUnitary
  norm_num [basisStates, List.all]
```

## 🎛️ CLI Options

```
python qasm_to_lean.py CIRCUIT1.QASM CIRCUIT2.QASM [OPTIONS]

Options:
  -l, --lemma NAME          Lemma name (default: equivalence_check)
  -o, --output FILE         Output file (default: stdout)
  --verify                  Run Lean verification
  --lean-project DIR        Lean project directory
  -n, --namespace NS        Lean namespace (default: SingleQubitCircuit)
```

## 🔧 Supported Gates

| QASM | Lean |
|------|------|
| `x`  | `X`  |
| `y`  | `Y`  |
| `z`  | `Z`  |
| `h`  | `H`  |
| `s`  | `S`  |
| `t`  | `T`  |
| `id` | `I`  |
| `sdg`| `Sdg`|
| `tdg`| `Tdg`|

## 🧪 Verification

✅ **Success**: `✓ Proof verified successfully by Lean! 🎉`
❌ **Failure**: Shows Lean error + suggestions

## 📁 File Structure

```
cli_tool/
├── qasm_to_lean.py     # Main converter (pure Python)
├── README.md           # This file
└── examples/           # Sample QASM files
    ├── hh.qasm
    ├── id.qasm
    └── ss_z.qasm
```

## 🎯 Minimal Design

- ✅ **Zero dependencies** (pure Python 3)
- ✅ **No installation** (just run)
- ✅ **Single file** (7621 bytes)
- ✅ **Self-contained** verification

## 🔗 Integration

Works with `Qamp352025/SingleQubitCircuit.lean`:

```bash
# Generate proof → Copy to Lean project → lake build
python qasm_to_lean.py ... -o my_proof.lean
lake build my_proof.lean
```

**Status**: ✅ Ready to test | **Size**: Minimal | **Dependencies**: None