module

public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.LocallyConstant.Basic
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LocallyConstantOfOpenSet

@[expose] public section

theorem UpperTheory.Reformulated.B.LocallyConstantOfKernelCapelliIdentities.locConst_of_ker :
    ∀ {G M : Type} [inst : Group G]
    [inst_1 : TopologicalSpace G] [IsTopologicalGroup G] [inst_3 : Group M] (χ : G →* M),
    IsOpen (↑χ.ker : Set G) → IsLocallyConstant (⇑χ : G → M) :=
  UpperTheory.Reformulated.B.LocallyConstantOfOpenSet.lc_of_open
