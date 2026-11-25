module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Ideal.Prime
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Noetherian.Basic

@[expose] public section

theorem UpperTheory.Reformulated.B.ZariskiNoetherianInduction.noetherian_induction_zariski :
    ∀ (k : Type) [inst : Field k] (n : ℕ) (Q : Set (Fin n → k) → Prop),
    Q ∅ →
      (∀ (s t : Set (Fin n → k)), s ⊆ t → Q t → Q s) →
        (∀ (s t : Set (Fin n → k)), Q s → Q t → Q (s ∪ t)) →
          (∀ (I : Ideal (MvPolynomial (Fin n) k)),
              I.IsPrime →
                ∃ g ∉ I,
                  Q
                    {c : Fin n → k |
                      (∀ p ∈ I, (MvPolynomial.eval c : MvPolynomial (Fin n) k → k) p = (0 : k)) ∧
                        (MvPolynomial.eval c : MvPolynomial (Fin n) k → k) g ≠ (0 : k)}) →
            Q Set.univ := by
  intro k inst n Q h0 hmono hunion hprime
  have key : ∀ I : Ideal (MvPolynomial (Fin n) k),
      Q {c : Fin n → k | ∀ p ∈ I, MvPolynomial.eval c p = 0} := by
    intro I
    induction I using IsNoetherian.induction with
    | _ I ih =>
      have step : ∀ g : MvPolynomial (Fin n) k, g ∉ I →
          Q {c : Fin n → k | (∀ p ∈ I, MvPolynomial.eval c p = 0) ∧
            MvPolynomial.eval c g = 0} := by
        intro g hg
        have hlt : I < I ⊔ Ideal.span {g} :=
          lt_of_le_of_ne le_sup_left fun h =>
            hg (h ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self g))
        refine hmono _ _ ?_ (ih _ hlt)
        rintro c ⟨hc, hcg⟩
        have hle : I ⊔ Ideal.span {g} ≤ RingHom.ker (MvPolynomial.eval c) :=
          sup_le (fun p hp => RingHom.mem_ker.2 (hc p hp))
            ((Ideal.span_singleton_le_iff_mem _).2 (RingHom.mem_ker.2 hcg))
        exact hle
      by_cases hP : Ideal.IsPrime I
      · obtain ⟨g, hg, hQ⟩ := hprime I hP
        refine hmono _ _ ?_ (hunion _ _ hQ (step g hg))
        intro c hc
        by_cases hcg : MvPolynomial.eval c g = 0
        · exact Or.inr ⟨hc, hcg⟩
        · exact Or.inl ⟨hc, hcg⟩
      · rcases Ideal.not_isPrime_iff.1 hP with htop | ⟨x, hx, y, hy, hxy⟩
        · refine hmono _ _ ?_ h0
          intro c hc
          simpa using hc 1 (htop ▸ Submodule.mem_top)
        · refine hmono _ _ ?_ (hunion _ _ (step x hx) (step y hy))
          intro c hc
          obtain h | h := mul_eq_zero.1 (map_mul (MvPolynomial.eval c) x y ▸ hc _ hxy)
          · exact Or.inl ⟨hc, h⟩
          · exact Or.inr ⟨hc, h⟩
  simpa using key (⊥ : Ideal (MvPolynomial (Fin n) k))
