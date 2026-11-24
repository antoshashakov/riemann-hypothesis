module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiagMod
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RootFFiniteGaloisIsPGroup
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

theorem _root_.GlobalTheory.T.rootF_finiteDimensional_isGalois_isPGroup : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), ∀ (l M₀ k n : ℕ), l.Prime → 0 < M₀ → l ∣ M₀ → ∀ U : X.K, Lev X (M₀ * l ^ k) U → FiniteDimensional (levF X M₀) (rootF X M₀ (M₀ * l ^ k) (l ^ n) U) ∧ IsGalois (levF X M₀) (rootF X M₀ (M₀ * l ^ k) (l ^ n) U) ∧ IsPGroup l (rootF X M₀ (M₀ * l ^ k) (l ^ n) U ≃ₐ[levF X M₀] rootF X M₀ (M₀ * l ^ k) (l ^ n) U) := by
  first | exact @GlobalTheory.KZ.ES.RootGal.rootF_finite_galois_isPGroup | exact GlobalTheory.KZ.ES.RootGal.rootF_finite_galois_isPGroup | (intros; apply GlobalTheory.KZ.ES.RootGal.rootF_finite_galois_isPGroup <;> assumption)
