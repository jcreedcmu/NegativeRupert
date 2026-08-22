module

public import KernelCaseAnalysis.Gen.Combine01
public import KernelCaseAnalysis.Gen.Validate0128
public import KernelCaseAnalysis.Gen.Validate0129
public import KernelCaseAnalysis.Gen.Validate0130
public import KernelCaseAnalysis.Gen.Validate0131
public import KernelCaseAnalysis.Gen.Validate0132
public import KernelCaseAnalysis.Gen.Validate0133
public import KernelCaseAnalysis.Gen.Validate0134
public import KernelCaseAnalysis.Gen.Validate0135
public import KernelCaseAnalysis.Gen.Validate0136
public import KernelCaseAnalysis.Gen.Validate0137
public import KernelCaseAnalysis.Gen.Validate0138
public import KernelCaseAnalysis.Gen.Validate0139
public import KernelCaseAnalysis.Gen.Validate0140
public import KernelCaseAnalysis.Gen.Validate0141
public import KernelCaseAnalysis.Gen.Validate0142
public import KernelCaseAnalysis.Gen.Validate0143
public import KernelCaseAnalysis.Gen.Validate0144
public import KernelCaseAnalysis.Gen.Validate0145
public import KernelCaseAnalysis.Gen.Validate0146
public import KernelCaseAnalysis.Gen.Validate0147

@[expose] public section

/-! GENERATED (scripts/gen_kernel_chunks.py): fold rows [0, 1119311). -/

namespace Noperthedron.Solution

private theorem c_1090770 : RangeOk getRow 1119311 0 1090770 :=
  combined_1086157.append (by norm_num) rangeOk_1086157_1090770
private theorem c_1094927 : RangeOk getRow 1119311 0 1094927 :=
  c_1090770.append (by norm_num) rangeOk_1090770_1094927
private theorem c_1097598 : RangeOk getRow 1119311 0 1097598 :=
  c_1094927.append (by norm_num) rangeOk_1094927_1097598
private theorem c_1100161 : RangeOk getRow 1119311 0 1100161 :=
  c_1097598.append (by norm_num) rangeOk_1097598_1100161
private theorem c_1101548 : RangeOk getRow 1119311 0 1101548 :=
  c_1100161.append (by norm_num) rangeOk_1100161_1101548
private theorem c_1103074 : RangeOk getRow 1119311 0 1103074 :=
  c_1101548.append (by norm_num) rangeOk_1101548_1103074
private theorem c_1105035 : RangeOk getRow 1119311 0 1105035 :=
  c_1103074.append (by norm_num) rangeOk_1103074_1105035
private theorem c_1106433 : RangeOk getRow 1119311 0 1106433 :=
  c_1105035.append (by norm_num) rangeOk_1105035_1106433
private theorem c_1107848 : RangeOk getRow 1119311 0 1107848 :=
  c_1106433.append (by norm_num) rangeOk_1106433_1107848
private theorem c_1109155 : RangeOk getRow 1119311 0 1109155 :=
  c_1107848.append (by norm_num) rangeOk_1107848_1109155
private theorem c_1111437 : RangeOk getRow 1119311 0 1111437 :=
  c_1109155.append (by norm_num) rangeOk_1109155_1111437
private theorem c_1112733 : RangeOk getRow 1119311 0 1112733 :=
  c_1111437.append (by norm_num) rangeOk_1111437_1112733
private theorem c_1113763 : RangeOk getRow 1119311 0 1113763 :=
  c_1112733.append (by norm_num) rangeOk_1112733_1113763
private theorem c_1114502 : RangeOk getRow 1119311 0 1114502 :=
  c_1113763.append (by norm_num) rangeOk_1113763_1114502
private theorem c_1115389 : RangeOk getRow 1119311 0 1115389 :=
  c_1114502.append (by norm_num) rangeOk_1114502_1115389
private theorem c_1116810 : RangeOk getRow 1119311 0 1116810 :=
  c_1115389.append (by norm_num) rangeOk_1115389_1116810
private theorem c_1117684 : RangeOk getRow 1119311 0 1117684 :=
  c_1116810.append (by norm_num) rangeOk_1116810_1117684
private theorem c_1118421 : RangeOk getRow 1119311 0 1118421 :=
  c_1117684.append (by norm_num) rangeOk_1117684_1118421
private theorem c_1119134 : RangeOk getRow 1119311 0 1119134 :=
  c_1118421.append (by norm_num) rangeOk_1118421_1119134
private theorem c_1119311 : RangeOk getRow 1119311 0 1119311 :=
  c_1119134.append (by norm_num) rangeOk_1119134_1119311

/-- Rows `[0, 1119311)` are valid. -/
theorem combined_1119311 : RangeOk getRow 1119311 0 1119311 := c_1119311

end Noperthedron.Solution

end
