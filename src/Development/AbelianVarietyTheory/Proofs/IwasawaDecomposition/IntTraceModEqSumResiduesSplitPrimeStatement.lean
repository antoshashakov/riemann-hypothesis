module

public import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntTraceModEqSumResiduesSplitPrime
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.intTrace_modEq_sum_residues_split_prime : ∀ {K : Type} [Field K] [NumberField K] (p : ℕ), p.Prime → ∀ {ι : Type} [Fintype ι] (e : ι → HeightOneSpectrum (𝓞 K)), Function.Injective e → (∀ W : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ W.asIdeal ↔ ∃ i, e i = W) → Fintype.card ι = Module.finrank ℚ K → ∀ (x : 𝓞 K) (b : ι → ℤ), (∀ i, x - (b i : 𝓞 K) ∈ (e i).asIdeal) → ((Algebra.intTrace ℤ (𝓞 K) x : ℤ) : ZMod p) = ∑ i, (b i : ZMod p) := by
  first | exact @GlobalTheory.SplitTrace.intTrace_modEq_sum | exact GlobalTheory.SplitTrace.intTrace_modEq_sum | (intros; apply GlobalTheory.SplitTrace.intTrace_modEq_sum <;> assumption)
