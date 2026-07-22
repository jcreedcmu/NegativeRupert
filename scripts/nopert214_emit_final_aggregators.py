#!/usr/bin/env python3
"""Emit the small aggregators for the final Nopert #214 formal proofs."""

import argparse
from pathlib import Path


LOCAL_KERNEL = """module

{imports}

@[expose] public section

namespace Noperthedron.Nopert214.GeneratedLocalViews

open AtlasProjectiveSolutionTree

def tables : SharedLocalTables :=
  ![{tables}]

theorem tables_valid_kernel : SharedLocalValid tables := by
  intro index
  fin_cases index
{proofs}

end Noperthedron.Nopert214.GeneratedLocalViews

end
"""


LOCAL_NATIVE = """module

{imports}

@[expose] public section

namespace Noperthedron.Nopert214.GeneratedLocalViewsNative

open AtlasProjectiveSolutionTree

def tables : SharedLocalTables :=
  ![{tables}]

theorem tables_valid : SharedLocalValid tables := by
  intro index
  fin_cases index
{proofs}

end Noperthedron.Nopert214.GeneratedLocalViewsNative

end
"""


FINAL_PROOF = """module

public import Noperthedron.Nopert214.IsNotRupert
public import Noperthedron.Nopert214.GeneratedChart0{suffix}
public import Noperthedron.Nopert214.GeneratedChart1{suffix}
public import Noperthedron.Nopert214.GeneratedChart2{suffix}
public import Noperthedron.Nopert214.FundamentalChart3

@[expose] public section

namespace Noperthedron.Nopert214.GeneratedProof{proof_suffix}

open AtlasProjectiveSolutionTree

def tables : CayleyAtlas.ChartIndex → Table :=
  ![GeneratedChart0{suffix}.table,
    GeneratedChart1{suffix}.table,
    GeneratedChart2{suffix}.table,
    FundamentalChart3.table]

theorem tables_chart : ∀ chart, (tables chart).chart = chart := by
  intro chart
  fin_cases chart <;> rfl

theorem tables_valid : ∀ chart, (tables chart).Valid := by
  intro chart
  fin_cases chart
  · exact GeneratedChart0{suffix}.table_valid_{validity}
  · exact GeneratedChart1{suffix}.table_valid_{validity}
  · exact GeneratedChart2{suffix}.table_valid_{validity}
  · exact FundamentalChart3.table_valid_{validity}

theorem exact_not_rupert : ¬ IsRupert exactVerts :=
  not_rupert_of_valid_tables tables tables_chart tables_valid

end Noperthedron.Nopert214.GeneratedProof{proof_suffix}

end
"""


def write(path, text):
    path.write_text(text, encoding="utf-8")
    print(f"wrote {path}")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("output_directory", type=Path)
    args = parser.parse_args()
    output = args.output_directory
    output.mkdir(parents=True, exist_ok=True)

    kernel_names = [f"GeneratedLocalView{i}SparseKernel" for i in range(4)]
    native_names = [f"GeneratedLocalView{i}Native" for i in range(4)]
    kernel_imports = "\n".join(
        f"public import Noperthedron.Nopert214.{name}"
        for name in kernel_names)
    native_imports = "\n".join(
        f"public import Noperthedron.Nopert214.{name}"
        for name in native_names)
    kernel_tables = ", ".join(f"some {name}.table"
                              for name in kernel_names)
    native_tables = ", ".join(f"some {name}.table"
                              for name in native_names)
    kernel_proofs = "\n".join(
        f"  · exact {name}.table_valid_kernel" for name in kernel_names)
    native_proofs = "\n".join(
        f"  · exact {name}.table_valid_native" for name in native_names)

    write(output / "GeneratedLocalViews.lean", LOCAL_KERNEL.format(
        imports=kernel_imports, tables=kernel_tables,
        proofs=kernel_proofs))
    write(output / "GeneratedLocalViewsNative.lean", LOCAL_NATIVE.format(
        imports=native_imports, tables=native_tables,
        proofs=native_proofs))
    write(output / "GeneratedProofKernel.lean", FINAL_PROOF.format(
        suffix="", proof_suffix="Kernel", validity="kernel"))
    write(output / "GeneratedProofNative.lean", FINAL_PROOF.format(
        suffix="Native", proof_suffix="Native", validity="native"))


if __name__ == "__main__":
    main()
