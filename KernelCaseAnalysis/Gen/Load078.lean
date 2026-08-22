module

public import Noperthedron.SolutionTable.Load
public meta import Noperthedron.SolutionTable.Load

@[expose] public section

/-! GENERATED (scripts/gen_kernel_chunks.py): rows [638976, 647168) of the solution
tree as literal 512-row chunks. Requires `solution_tree_v7.csv` at the repo
root. -/

namespace Noperthedron.Solution

load_csv_chunks_curried "solution_tree_v7.csv" from 638976 to 647168 chunkSize 512

end Noperthedron.Solution

end
