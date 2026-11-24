module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatCardHomologyOfShortExactMul
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open CategoryTheory Limits

theorem _root_.GlobalTheory.T.natCard_homology_of_shortExact_mul' : ∀ (p : ℕ) (C G : CochainComplex (ModuleCat.{0} ℤ) ℕ) (π : C ⟶ G) (hz : ((p : ℤ) • 𝟙 C) ≫ π = 0), (ShortComplex.mk ((p : ℤ) • 𝟙 C) π hz).ShortExact → ∀ n : ℕ, Nat.card (G.homology n) = Nat.card ((C.homology n) ⧸ LinearMap.range ((p : ℤ) • (LinearMap.id : C.homology n →ₗ[ℤ] C.homology n))) * Nat.card (LinearMap.ker ((p : ℤ) • (LinearMap.id : C.homology (n + 1) →ₗ[ℤ] C.homology (n + 1)))) := by
  first | exact @GlobalTheory.natCard_homology_of_shortExact_mul | exact GlobalTheory.natCard_homology_of_shortExact_mul | (intros; apply GlobalTheory.natCard_homology_of_shortExact_mul <;> assumption)
