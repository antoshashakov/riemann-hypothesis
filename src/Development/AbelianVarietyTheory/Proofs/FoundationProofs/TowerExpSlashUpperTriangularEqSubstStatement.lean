module

public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerExpSlashUpperTriangularEqSubst
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion

theorem _root_.GlobalTheory.T.tower_exp_slash_upperTriangular_eq_subst : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (g : GQ), ent g 1 0 = 0 → ∀ f : X.K,
  X.exp (X.sl g f) = sub ε (ent g 0 0) (ent g 0 1) (ent g 1 1) (X.exp f) := by
  first | exact @GlobalTheory.CyclotomicQExpansion.exp_sl_upper | exact GlobalTheory.CyclotomicQExpansion.exp_sl_upper | (intros; apply GlobalTheory.CyclotomicQExpansion.exp_sl_upper <;> assumption)
