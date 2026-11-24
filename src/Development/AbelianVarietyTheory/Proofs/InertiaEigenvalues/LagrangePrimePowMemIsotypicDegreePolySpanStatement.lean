module

public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ImageStableDegreeBounds
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.RepresentationBounds
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LagrangePrimePowMemIsotypicDegreePolySpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MathlibImports

@[expose] public section

open PowerSeries GlobalTheory.BK

theorem _root_.GlobalTheory.T.lagrange_prime_pow_mem_isotypicDegreePoly_span : ∀ (l e a : ℕ) [Fact l.Prime], 1 ≤ a → e + 1 = l ^ a → ∀ (Sig : Finset (ZMod e)) (c : ZMod e) (A' N : ℕ), Sig.card ≤ N → 2 * A' + 2 < l → ∃ α β : Polynomial ℤ_[l], Polynomial.C ((l : ℤ_[l]) ^ GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.rho l Sig N) = α * (GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.P₁ Sig c A').map (Int.castRingHom ℤ_[l]) + β * (GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.P₂ Sig c A').map (Int.castRingHom ℤ_[l]) := by
  first | exact @GlobalTheory.lagrange_C_rho_eq_comb_degrees | exact GlobalTheory.lagrange_C_rho_eq_comb_degrees | (intros; apply GlobalTheory.lagrange_C_rho_eq_comb_degrees <;> assumption)
