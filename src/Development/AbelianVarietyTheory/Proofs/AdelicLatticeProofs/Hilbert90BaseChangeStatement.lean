module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.TensorProduct.Maps
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Hilbert90BaseChange
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub

@[expose] public section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

theorem _root_.GlobalTheory.T.hilbert90_baseChange' : ∀ (F E K : Type) [Field F] [CharZero F] [Field E] [Algebra F E] [FiniteDimensional F E] [Field K] [Algebra F K] (τ : E ≃ₐ[F] E) (m : ℕ), orderOf τ = m → ∀ x : K ⊗[F] E, ∏ i ∈ Finset.range m, (Algebra.TensorProduct.map (AlgHom.id K K) (τ : E →ₐ[F] E))^[i] x = 1 → ∃ z : (K ⊗[F] E)ˣ, x * Algebra.TensorProduct.map (AlgHom.id K K) (τ : E →ₐ[F] E) z = z := by
  first | exact @GlobalTheory.CNorm.hilbert90_baseChange | exact GlobalTheory.CNorm.hilbert90_baseChange | (intros; apply GlobalTheory.CNorm.hilbert90_baseChange <;> assumption)
