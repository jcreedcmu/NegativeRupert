module

public import KernelCaseAnalysis.Gen.Combine00
public import KernelCaseAnalysis.Gen.Validate0064
public import KernelCaseAnalysis.Gen.Validate0065
public import KernelCaseAnalysis.Gen.Validate0066
public import KernelCaseAnalysis.Gen.Validate0067
public import KernelCaseAnalysis.Gen.Validate0068
public import KernelCaseAnalysis.Gen.Validate0069
public import KernelCaseAnalysis.Gen.Validate0070
public import KernelCaseAnalysis.Gen.Validate0071

@[expose] public section

/-! GENERATED (scripts/gen_kernel_chunks.py): fold rows [0, 975329). -/

namespace Noperthedron.Solution

private theorem c_952665 : RangeOk getRow 975329 0 952665 :=
  combined_949184.append (by norm_num) rangeOk_949184_952665
private theorem c_959985 : RangeOk getRow 975329 0 959985 :=
  c_952665.append (by norm_num) rangeOk_952665_959985
private theorem c_963692 : RangeOk getRow 975329 0 963692 :=
  c_959985.append (by norm_num) rangeOk_959985_963692
private theorem c_966597 : RangeOk getRow 975329 0 966597 :=
  c_963692.append (by norm_num) rangeOk_963692_966597
private theorem c_970165 : RangeOk getRow 975329 0 970165 :=
  c_966597.append (by norm_num) rangeOk_966597_970165
private theorem c_972828 : RangeOk getRow 975329 0 972828 :=
  c_970165.append (by norm_num) rangeOk_970165_972828
private theorem c_975203 : RangeOk getRow 975329 0 975203 :=
  c_972828.append (by norm_num) rangeOk_972828_975203
private theorem c_975329 : RangeOk getRow 975329 0 975329 :=
  c_975203.append (by norm_num) rangeOk_975203_975329

/-- Rows `[0, 975329)` are valid. -/
theorem combined_975329 : RangeOk getRow 975329 0 975329 := c_975329

end Noperthedron.Solution

end
