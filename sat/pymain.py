from uuid import uuid4
from qiskit import transpile
from qiskit.circuit import QuantumCircuit, QuantumRegister, ClassicalRegister
from qiskit_aer import AerSimulator
from qiskit.providers.backend import Backend
from random import randint

# global circuits cache, avoid passing complex objects across languages
CIRCUITS_CACHE: dict[str, QuantumCircuit] = dict()


def run_grover(oracle_id: str, n_vars: int, n_ancillas: int, max_iterations: int) -> list[str]:
    """Wrapper to run BBHT grover from SWIpl"""
    oracle = CIRCUITS_CACHE[oracle_id]  # get the oracle from the cache
    iterations = randint(1, max_iterations)  # get random iteration amount for this bound
    circ = grover(oracle, iterations, n_vars, n_ancillas)  # build circuit
    simulator = AerSimulator()
    opt_circ = transpile(circ, backend=simulator, optimization_level=3)  # optimize it for simulation (should not be necessary)
    return list(simulator.run(opt_circ, shots=16).result().get_counts().keys())  # run and return possibly satisfying bitstrings to SWIpl


def grover(oracle: QuantumCircuit, iterations: int, n_vars: int, n_ancillas: int, n_outputs: int = 1) -> QuantumCircuit:
    """Build the circuit for grover's algorithm using ancillas"""
    var = QuantumRegister(n_vars, name="var")  # variable register to search on
    ancilla = QuantumRegister(n_ancillas, name="anc")  # ancillas, not used for search
    output = QuantumRegister(n_outputs, name="out")  # output register
    measure = ClassicalRegister(n_vars, name="meas")  # classical register for measurements
    qc = QuantumCircuit(var, ancilla, output, measure)

    # state preparation
    qc.h(var)
    qc.x(output)
    qc.h(output)

    # build the iterated operator
    operator = QuantumCircuit(var, ancilla, output)
    # operator.barrier()
    operator.compose(oracle, inplace=True)  # oracle
    var_idx = list(range(n_vars))
    # build the diffuser
    operator.h(var_idx)  # state preparation at beginning of diffuser
    operator.x(var_idx)
    # multi controlled z
    operator.h(var_idx[-1])
    operator.mcx(var_idx[:-1], var_idx[-1])
    operator.h(var_idx[-1])

    operator.x(var_idx)
    operator.h(var_idx)  # state preparation at end of diffuser

    qc.compose(operator.power(iterations), inplace=True)
    qc.measure(var, measure)
    return qc


def sat_oracle(CNF: list[tuple[list[int], list[int]]], n: int, backend: Backend | None = None) -> QuantumCircuit:
    """Create a multiple-ancilla sat oracle"""
    var = QuantumRegister(n, name="var")
    clauses = QuantumRegister(len(CNF), name="clauses")
    output = QuantumRegister(1, name="out")
    oracle = QuantumCircuit(var, clauses, output)
    # track clause falsification in ancillas
    for j, (negated, straight) in enumerate(CNF):
        # straight literals falsify if false
        for s in straight:
            oracle.x(var[s])
        oracle.mcx([var[v] for v in negated + straight], clauses[j])
        # restore qubit for the next clause
        for s in straight:
            oracle.x(var[s])
    # phase kickback
    oracle.x(clauses)
    oracle.mcx(list(clauses), output[0])
    oracle.x(clauses)
    # uncompute ancillas for next iteration
    for j in range(len(CNF) - 1, -1, -1):
        negated, straight = CNF[j]
        for s in straight:
            oracle.x(var[s])
        oracle.mcx([var[v] for v in negated + straight], clauses[j])
        for s in straight:
            oracle.x(var[s])
    if backend is None:
        backend = AerSimulator()
    oracle_opt = transpile(oracle, backend=backend, optimization_level=3)
    return oracle_opt


def oracle(CNF: list[tuple[list[str], list[str]]]) -> tuple[str, list[str]]:
    name_to_index = {
        name: idx for idx, name in
        enumerate(sorted({name
                          for item in CNF
                          for sublist in item
                          for name in sublist}
                         ))
    }
    CNF_int = [
        ([name_to_index[name] for name in left],
         [name_to_index[name] for name in right])
        for left, right in CNF
    ]
    oracle = sat_oracle(CNF_int, len(name_to_index))
    names = [t[0] for t in sorted(name_to_index.items(), key=lambda t: t[1])]
    oracle_id = str(uuid4())
    CIRCUITS_CACHE[oracle_id] = oracle
    return oracle_id, names
