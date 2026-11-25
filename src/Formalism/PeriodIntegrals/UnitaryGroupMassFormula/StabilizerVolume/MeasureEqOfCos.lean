module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.CosDens
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.MeasureEqOfCos

@[expose] public section

noncomputable section

namespace PI.VolStabS

open MeasureTheory Topology Set Filter

section CosMeas

variable {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
  [MeasurableSpace X] [OpensMeasurableSpace X]


omit [MeasurableSpace X] [OpensMeasurableSpace X] in
def thick (S : Set X) (Λ : AddSubgroup X) : Set X := {x | ∃ s ∈ S, x - s ∈ Λ}

omit [MeasurableSpace X] [OpensMeasurableSpace X] in
theorem isOpen_thick (S : Set X) (Λ : AddSubgroup X) (hΛ : IsOpen (Λ : Set X)) :
    IsOpen (thick S Λ) := by
  have e : thick S Λ = ⋃ s ∈ S, (fun x => x - s) ⁻¹' (Λ : Set X) := by
    ext x
    simp [thick]
  rw [e]
  exact isOpen_biUnion fun s _ => hΛ.preimage (continuous_id.sub continuous_const)

theorem measure_thick_eq (m1 m2 : Measure X) (Λ : AddSubgroup X) (hΛ : IsOpen (Λ : Set X))
    (h : ∀ y, m1 {z | z - y ∈ Λ} = m2 {z | z - y ∈ Λ}) (S : Set X) (hS : IsCompact S) :
    m1 (thick S Λ) = m2 (thick S Λ) := by
  classical

  have hfib : ∀ c : X ⧸ Λ, m1 (((↑) : X → X ⧸ Λ) ⁻¹' {c}) = m2 (((↑) : X → X ⧸ Λ) ⁻¹' {c}) ∧
      MeasurableSet (((↑) : X → X ⧸ Λ) ⁻¹' {c}) := by
    intro c
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective c
    have e : ((↑) : X → X ⧸ Λ) ⁻¹' {(y : X ⧸ Λ)} = {z | z - y ∈ Λ} := by
      ext z
      simp [QuotientAddGroup.eq_iff_sub_mem]
    rw [e]
    exact ⟨h y, (hΛ.preimage (continuous_id.sub continuous_const)).measurableSet⟩
  obtain ⟨t, ht⟩ := hS.elim_finite_subcover (fun s : S => {z : X | z - (s : X) ∈ Λ})
    (fun s => hΛ.preimage (continuous_id.sub continuous_const))
    (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, by simp⟩)
  have hT : thick S Λ = ⋃ c ∈ t.image (fun s : S => ((s : X) : X ⧸ Λ)),
      ((↑) : X → X ⧸ Λ) ⁻¹' {c} := by
    ext x
    simp only [thick, mem_ofPred_eq, mem_iUnion, mem_preimage, mem_singleton_iff,
      Finset.mem_image, exists_prop]
    constructor
    · rintro ⟨s, hs, hxs⟩
      obtain ⟨s', hs't, hss'⟩ := mem_iUnion₂.mp (ht hs)
      refine ⟨((s' : X) : X ⧸ Λ), ⟨s', hs't, rfl⟩, ?_⟩
      rw [QuotientAddGroup.eq_iff_sub_mem]
      have e : x - (s' : X) = (x - s) + (s - s') := by abel
      rw [e]
      exact Λ.add_mem hxs hss'
    · rintro ⟨c, ⟨s', _, rfl⟩, hx⟩
      exact ⟨s', s'.2, (QuotientAddGroup.eq_iff_sub_mem).mp hx⟩
  rw [hT, measure_biUnion_finset, measure_biUnion_finset]
  · exact Finset.sum_congr rfl fun c _ => (hfib c).1
  all_goals first
    | exact fun c _ c' _ hne => (Set.disjoint_singleton.mpr hne).preimage _
    | exact fun c _ => (hfib c).2


omit [MeasurableSpace X] [OpensMeasurableSpace X] in
theorem iInter_thick (S : Set X) (hSc : IsClosed S) (Λ : ℕ → AddSubgroup X)
    (hb : ∀ N ∈ 𝓝 (0 : X), ∃ n, (Λ n : Set X) ⊆ N) : ⋂ n, thick S (Λ n) = S := by
  ext x
  simp only [mem_iInter]
  constructor
  · intro hx
    by_contra hxS
    have hN : (fun u => x - u) ⁻¹' Sᶜ ∈ 𝓝 (0 : X) := by
      apply (continuous_const.sub continuous_id).continuousAt.preimage_mem_nhds
      simpa using hSc.isOpen_compl.mem_nhds hxS
    obtain ⟨n, hn⟩ := hb _ hN
    obtain ⟨s, hs, hxs⟩ := hx n
    have hmem := hn hxs
    simp only [mem_preimage, mem_compl_iff, sub_sub_cancel] at hmem
    exact hmem hs
  · intro hx n
    exact ⟨x, hx, by simp⟩

theorem measure_eq_of_cos (m1 m2 : Measure X) [IsFiniteMeasure m1]
    (Λ : ℕ → AddSubgroup X) (hΛo : ∀ n, IsOpen (Λ n : Set X)) (hanti : Antitone Λ)
    (hb : ∀ N ∈ 𝓝 (0 : X), ∃ n, (Λ n : Set X) ⊆ N)
    (h : ∀ n y, m1 {z | z - y ∈ Λ n} = m2 {z | z - y ∈ Λ n})
    (S : Set X) (hS : IsCompact S) (hSc : IsClosed S) : m1 S = m2 S := by
  have hmono : Antitone fun n => thick S (Λ n) := by
    intro a c hac x hx
    obtain ⟨s, hs, hxs⟩ := hx
    exact ⟨s, hs, hanti hac hxs⟩
  have hnull : ∀ (μ : Measure X) n, NullMeasurableSet (thick S (Λ n)) μ := fun μ n =>
    (isOpen_thick S (Λ n) (hΛo n)).measurableSet.nullMeasurableSet
  have heq : ∀ n, m1 (thick S (Λ n)) = m2 (thick S (Λ n)) := fun n =>
    measure_thick_eq m1 m2 (Λ n) (hΛo n) (h n) S hS
  rw [← iInter_thick S hSc Λ hb, hmono.measure_iInter (hnull m1) ⟨0, measure_ne_top _ _⟩,
    hmono.measure_iInter (hnull m2) ⟨0, by rw [← heq 0]; exact measure_ne_top _ _⟩]
  simp only [heq]

end CosMeas

theorem cosDens_holds : CosDens :=
  _root_.PI.VolStabSW.cosDens_holds

end PI.VolStabS
