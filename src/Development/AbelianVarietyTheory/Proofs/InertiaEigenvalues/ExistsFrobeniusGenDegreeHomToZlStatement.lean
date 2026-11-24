module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusGenDegreeHomToZl
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MathlibImports
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles

@[expose] public section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries

theorem _root_.GlobalTheory.T.exists_frobenius_gen_degree_hom_to_Zl : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l), ∃ (F : ↥(GK K)) (ν : ↥(GK K) →* Multiplicative ℤ_[l]), Continuous ν ∧ (∀ σ ∈ IK K, ν σ = 1) ∧ ν F = Multiplicative.ofAdd 1 ∧ (Subgroup.closure (insert F (IK K : Set ↥(GK K)))).topologicalClosure = ⊤ := by
  first | exact @GlobalTheory.UnramGen.exists_gen_degree | exact GlobalTheory.UnramGen.exists_gen_degree | (intros; apply GlobalTheory.UnramGen.exists_gen_degree <;> assumption)
