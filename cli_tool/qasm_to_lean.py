#!/usr/bin/env python3
"""
OpenQASM to Lean Converter with Verification
QAMP 2025 Project #35

Parses OpenQASM 3.0 single-qubit circuits, generates Lean 4 proof code,
and optionally verifies the proof using Lean compiler.
"""

import re
import sys
import subprocess
import tempfile
import os
from typing import List, Tuple

class QASMToLean:
    """Converts OpenQASM 3.0 single-qubit circuits to Lean 4 code"""
    
    GATE_MAP = {
        'x': 'X',
        'y': 'Y', 
        'z': 'Z',
        'h': 'H',
        's': 'S',
        't': 'T',
        'id': 'I',
        'sdg': 'Sdg',
        'tdg': 'Tdg',
    }
    
    def parse_qasm(self, qasm_code: str) -> List[str]:
        """Parse QASM code and extract gate sequence"""
        gates = []
        lines = qasm_code.strip().split('\n')
        
        for line in lines:
            line = line.strip()
            if (not line or line.startswith('//') or 
                line.startswith('OPENQASM') or line.startswith('include') or
                line.startswith('qubit')):
                continue
            
            # Parse standard gates
            match = re.match(r'([a-z]+)\s+q\[\d+\];', line)
            if match:
                gate_name = match.group(1)
                if gate_name in self.GATE_MAP:
                    gates.append(self.GATE_MAP[gate_name])
                continue
        
        return gates
    
    def generate_circuit_def(self, name: str, gates: List[str]) -> str:
        """Generate Lean circuit definition"""
        if not gates:
            return f"def {name} : Circuit := []"
        
        gate_list = ", ".join([f".{g}" for g in gates])
        return f"def {name} : Circuit := [{gate_list}]"
    
    def generate_equivalence_lemma(self, name: str, circuit1_name: str, 
                                   circuit2_name: str) -> str:
        """Generate Lean equivalence lemma"""
        return f"""lemma {name} : circuitsEq {circuit1_name} {circuit2_name} = true := by
  unfold circuitsEq evalCircuit Gate.toUnitary
  norm_num [basisStates, List.all, Qubit.H_sq, Qubit.X_sq, Qubit.Z_sq]"""
    
    def qasm_to_lean(self, qasm1: str, qasm2: str, 
                     lemma_name: str = "equivalence_check",
                     namespace: str = "SingleQubitCircuit") -> str:
        """Convert two QASM circuits to a complete Lean equivalence proof"""
        
        gates1 = self.parse_qasm(qasm1)
        gates2 = self.parse_qasm(qasm2)
        
        circuit1_name = "circuit1"
        circuit2_name = "circuit2"
        
        # Generate Lean code
        output = []
        output.append("-- Auto-generated from OpenQASM 3.0")
        output.append(f"import {namespace}")
        output.append("")
        output.append(f"namespace {namespace}")
        output.append("")
        output.append(self.generate_circuit_def(circuit1_name, gates1))
        output.append(self.generate_circuit_def(circuit2_name, gates2))
        output.append("")
        output.append(self.generate_equivalence_lemma(
            lemma_name, circuit1_name, circuit2_name))
        output.append("")
        output.append(f"end {namespace}")
        
        return "\n".join(output)

def verify_with_lean(lean_code: str, lean_project_dir: str = None) -> Tuple[bool, str]:
    """
    Verify the generated Lean code using Lean compiler
    
    Args:
        lean_code: The Lean code to verify
        lean_project_dir: Path to your Lean project directory (optional)
    
    Returns:
        (success: bool, message: str)
    """
    
    # Create a temporary file for the Lean code
    with tempfile.NamedTemporaryFile(mode='w', suffix='.lean', delete=False) as f:
        temp_file = f.name
        f.write(lean_code)
    
    try:
        # Try to compile with lean directly (if in a Lean project)
        if lean_project_dir:
            result = subprocess.run(
                ['lake', 'build', os.path.basename(temp_file)],
                cwd=lean_project_dir,
                capture_output=True,
                text=True,
                timeout=3000
            )
        else:
            # Just check syntax with lean command
            result = subprocess.run(
                ['lean', temp_file],
                capture_output=True,
                text=True,
                timeout=30
            )
        
        if result.returncode == 0:
            return True, "✓ Proof verified successfully by Lean!"
        else:
            error_msg = result.stderr if result.stderr else result.stdout
            return False, f"✗ Lean verification failed:\n{error_msg}"
    
    except subprocess.TimeoutExpired:
        return False, "✗ Lean verification timed out (>30s)"
    except FileNotFoundError:
        return False, "✗ Lean not found. Please install Lean 4 or provide --no-verify flag"
    except Exception as e:
        return False, f"✗ Error during verification: {str(e)}"
    finally:
        # Clean up temp file
        if os.path.exists(temp_file):
            os.unlink(temp_file)

def main():
    import argparse
    
    parser = argparse.ArgumentParser(
        description='Convert OpenQASM circuits to Lean proofs and optionally verify them',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Generate Lean code only
  python qasm_to_lean.py hh.qasm id.qasm -l hTwiceIsId -o output.lean
  
  # Generate and verify with Lean
  python qasm_to_lean.py hh.qasm id.qasm -l hTwiceIsId --verify
  
  # Verify in a specific Lean project
  python qasm_to_lean.py hh.qasm id.qasm --verify --lean-project ./my-lean-project
        """
    )
    
    parser.add_argument('circuit1', help='First OpenQASM circuit file')
    parser.add_argument('circuit2', help='Second OpenQASM circuit file')
    parser.add_argument('-l', '--lemma', default='equivalence_check',
                       help='Name for the Lean lemma (default: equivalence_check)')
    parser.add_argument('-o', '--output', help='Output .lean file (default: stdout)')
    parser.add_argument('--verify', action='store_true',
                       help='Verify the proof with Lean compiler')
    parser.add_argument('--lean-project', help='Path to Lean project directory')
    parser.add_argument('-n', '--namespace', default='SingleQubitCircuit',
                       help='Lean namespace (default: SingleQubitCircuit)')
    
    args = parser.parse_args()
    
    # Read QASM files
    try:
        with open(args.circuit1, 'r') as f:
            qasm1 = f.read()
        with open(args.circuit2, 'r') as f:
            qasm2 = f.read()
    except FileNotFoundError as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)
    
    # Convert to Lean
    converter = QASMToLean()
    lean_code = converter.qasm_to_lean(qasm1, qasm2, args.lemma, args.namespace)
    
    # Output to file or stdout
    if args.output:
        with open(args.output, 'w') as f:
            f.write(lean_code)
        print(f"✓ Generated Lean code: {args.output}")
    else:
        print(lean_code)
        print()  # Blank line separator
    
    # Verify with Lean if requested
    if args.verify:
        print("\n" + "="*60)
        print("Running Lean verification...")
        print("="*60)
        
        success, message = verify_with_lean(lean_code, args.lean_project)
        print(message)
        
        if success:
            print("\n🎉 Circuits are formally proven equivalent!")
            sys.exit(0)
        else:
            print("\n⚠️  Verification failed. Check your Lean installation and project setup.")
            sys.exit(1)

if __name__ == "__main__":
    main()
