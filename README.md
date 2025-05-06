# DynamicCaDiCaL

DynamicCaDiCaL is a SAT solver based on the CaDiCaL solver, which implements dynamic parameter tuning and advanced techniques for SAT solving. It is designed to test different configurations and performance of the solver in various benchmarks.

## Features

- Based on the CaDiCaL SAT solver
- Dynamic parameter tuning and multi-armed bandit algorithms
- Supports benchmark instance input and outputs results for SAT and UNSAT cases
- Generates DRAT proofs for UNSAT instances

## Installation

### Prerequisites

- Git
- CMake
- A C++ compiler (e.g., GCC)

### Clone the Repository

```bash
gitgit clone https://github.com/xujunjie23/Dynamiccadical.git
cd dynamiccadical

###Build the Solver
After cloning the repository, you can build the solver by running the following command:

bash
复制
编辑
./build.sh
This will build the solver using the provided Docker environment.

Now that the solver is built, you can proceed to run it on different CNF files.

Running the Solver
bash
复制
编辑
./run.sh <path_to_benchmark_cnf> <output_directory>
<path_to_benchmark_cnf>: Path to the CNF benchmark file.

<output_directory>: Directory where the proof (for UNSAT cases) will be saved.

For example:

bash
复制
编辑
./run.sh /path/to/benchmark.cnf ./output
Example Output
For SAT instances: The solution will be printed to the console.

For UNSAT instances: A DRAT proof file (proof.out) will be saved in the specified output directory.

Contributing
Feel free to fork this repository and submit pull requests. We welcome contributions from the community.

License
Distributed under the MIT License. See LICENSE for more information.
