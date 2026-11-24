module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Letter
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularTowerClassEqImpPowRatio
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AbelianVarietyTheory.Definitions.Foundations.EeProd
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed

@[expose] public section

open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups

theorem _root_.GlobalTheory.T.modularTower_class_eq_imp_pow_ratio : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) (f f' : X.Kˣ), X.cls l n f = X.cls l n f' → ∃ u : X.Kˣ, (f' : X.K) = f * (u : X.K) ^ (l ^ n) := by
  first | exact @GlobalTheory.Tower.cls_eq_pow | exact GlobalTheory.Tower.cls_eq_pow | (intros; apply GlobalTheory.Tower.cls_eq_pow <;> assumption)
