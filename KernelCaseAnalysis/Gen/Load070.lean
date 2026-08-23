module

public import Noperthedron.SolutionTable.Load
public meta import Noperthedron.SolutionTable.Load

@[expose] public section

/-! GENERATED (scripts/gen_kernel_chunks.py): rows [573440, 581632) of the solution
tree as literal 512-row chunks. Requires `solution_tree_v8.csv` at the repo
root. -/

namespace Noperthedron.Solution

load_csv_chunks_curried "solution_tree_v8.csv" from 573440 to 581632 chunkSize 512

end Noperthedron.Solution

end
