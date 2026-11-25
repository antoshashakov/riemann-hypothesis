module

public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.LocallyConstant.Basic
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LocallyConstantOfOpenSet

@[expose] public section

theorem UpperTheory.Reformulated.B.LocallyConstantOfKernel.lc_of_ker :
    ∀ {Γ C : Type} [inst : Group Γ]
    [inst_1 : TopologicalSpace Γ] [IsTopologicalGroup Γ] [inst_3 : Group C] (η : Γ →* C),
    IsOpen (↑η.ker : Set Γ) → IsLocallyConstant (⇑η : Γ → C) :=
  UpperTheory.Reformulated.B.LocallyConstantOfOpenSet.lc_of_open
