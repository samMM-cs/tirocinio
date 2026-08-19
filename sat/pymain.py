from uuid import uuid4
from time import perf_counter
from qiskit import transpile
from qiskit.circuit import QuantumCircuit, QuantumRegister, ClassicalRegister
from qiskit_aer import AerSimulator
from qiskit.providers.backend import Backend
from random import randint

# global circuits cache, avoid passing complex objects across languages
CIRCUITS_CACHE: dict[str, QuantumCircuit] = dict()


def run_grover(oracle_id: str, n_vars: int, n_ancillas: int, max_iterations: int) -> tuple[list[str], dict]:
    """Wrapper to run BBHT grover from SWIpl.

    Returns (bitstrings, metrics) where metrics carries the per-attempt data
    needed for the resource/scaling evaluation (iterations actually used,
    simulation wall-clock time, shots, and the full observed-counts histogram).
    """
    oracle = CIRCUITS_CACHE[oracle_id]  # get the oracle from the cache
    iterations = randint(1, max_iterations)  # get random iteration amount for this bound
    circ = grover(oracle, iterations, n_vars, n_ancillas)  # build circuit
    simulator = AerSimulator()
    sim_start = perf_counter()
    opt_circ = transpile(circ, backend=simulator, optimization_level=3)  # optimize it for simulation (should not be necessary)
    shots = 16
    counts = simulator.run(opt_circ, shots=shots).result().get_counts()
    sim_time = perf_counter() - sim_start
    metrics = {
        "iterations_used": iterations,
        "max_iterations": max_iterations,
        "sim_time": sim_time,
        "shots": shots,
        "counts": dict(counts),
    }
    return list(counts.keys()), metrics


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


def sat_oracle(CNF: list[tuple[list[int], list[int]]], n: int, backend: Backend | None = None) -> tuple[QuantumCircuit, dict]:
    """Create a multiple-ancilla sat oracle.

    Returns (oracle_opt, metrics) where metrics reports the circuit-resource
    figures needed for the preprocessing-impact evaluation: qubit/ancilla
    counts, the (pre-transpile) number of multi-controlled-X gates the
    construction used, and the transpiled circuit's depth, gate counts and
    build time.
    """
    n_clauses = len(CNF)
    var = QuantumRegister(n, name="var")
    clauses = QuantumRegister(n_clauses, name="clauses")
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
    mcx_count = oracle.count_ops().get("mcx", 0)  # design-level count, pre-transpile
    if backend is None:
        backend = AerSimulator()
    build_start = perf_counter()
    oracle_opt = transpile(oracle, backend=backend, optimization_level=3)
    build_time = perf_counter() - build_start
    metrics = {
        "n_vars": n,
        "n_clauses": n_clauses,
        "n_qubits": oracle.num_qubits,
        "n_ancillas": n_clauses + 1,  # clause ancillas + output qubit
        "mcx_count": mcx_count,
        "depth": oracle_opt.depth(),
        "gate_counts": dict(oracle_opt.count_ops()),
        "build_time": build_time,
    }
    return oracle_opt, metrics


def oracle(CNF: list[tuple[list[str], list[str]]]) -> tuple[str, list[str], dict]:
    # print(CNF)
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
    oracle_circ, metrics = sat_oracle(CNF_int, len(name_to_index))
    names = [t[0] for t in sorted(name_to_index.items(), key=lambda t: t[1])]
    oracle_id = str(uuid4())
    CIRCUITS_CACHE[oracle_id] = oracle_circ
    return oracle_id, names, metrics


if __name__ == "__main__":
    oracle([(["A"], ["A"])])
