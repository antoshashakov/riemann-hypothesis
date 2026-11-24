module

public import Development.AbelianVarietyTheory.Definitions.Foundations.ExpUpper
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerGaloisActionPreservesGammaLevel
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

theorem _root_.GlobalTheory.T.towerGaloisAction_preserves_gammaLevel : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (M : ℕ) (s : Ω ≃ₐ[ℚ] Ω) (f : X.K), 0 < M → (∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) f = f) → ∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) (X.gal s f) = X.gal s f := by
  first | exact @GlobalTheory.Tower.gal_level | exact GlobalTheory.Tower.gal_level | (intros; apply GlobalTheory.Tower.gal_level <;> assumption)
