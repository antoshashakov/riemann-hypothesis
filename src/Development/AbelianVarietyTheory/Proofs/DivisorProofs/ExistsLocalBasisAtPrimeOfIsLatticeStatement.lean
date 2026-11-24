module

public import Mathlib.Algebra.Module.Lattice.Full
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalBasisAtPrimeOfIsLattice
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open NumberField IsDedekindDomain
open scoped Matrix

theorem _root_.GlobalTheory.T.exists_localBasis_at_prime_of_isLattice : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), L.IsFullLattice E → ∃ X : Matrix (Fin n) (Fin n) E, IsUnit X.det ∧ (∀ j, (fun i => X i j) ∈ L) ∧ ∀ x ∈ L, ∀ i, w.valuation E ((X⁻¹ *ᵥ x) i) ≤ 1 := by
  exact @GlobalTheory.exists_local_basis_of_isLattice
