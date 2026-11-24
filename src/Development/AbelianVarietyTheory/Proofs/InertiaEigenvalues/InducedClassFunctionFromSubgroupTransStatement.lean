module

public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Mathlib.Basic.Complex.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InducedClassFunctionFromSubgroupTrans
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IndApplyOne

@[expose] public section

open GlobalTheory.BI GlobalTheory.BrauerZero

theorem _root_.GlobalTheory.T.inducedClassFunctionFromSubgroup_trans : ∀ {G : Type} [Group G] [Finite G] (K A : Subgroup G), K ≤ A → ∀ (ψ : K → ℂ), ind A (ind (K.subgroupOf A) (fun k => ψ ⟨((k : A) : G), k.2⟩)) = ind K ψ := by
  first | exact @GlobalTheory.BrauerZero.ind_ind_of_le | exact GlobalTheory.BrauerZero.ind_ind_of_le | (intros; apply GlobalTheory.BrauerZero.ind_ind_of_le <;> assumption)
