module

public import Formalism.CyclotomicNorms.StatementI
public import Mathlib.Order.CompletePartialOrder
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
public import Mathlib.NumberTheory.LucasPrimality
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

namespace Formalism.BasicNotions.Examples₂

theorem mem_of_dvd_prod_pow {l : ℕ} (hl : l.Prime) (ps : List ℕ) (K : ℕ) (hp : ∀ p ∈ ps, p.Prime)
    (h : l ∣ ps.prod ^ K) : l ∈ ps := by
  have h' : l ∣ ps.prod := (Nat.Prime.prime hl).dvd_of_dvd_pow h
  obtain ⟨p, hps, hlp⟩ := ((Nat.Prime.prime hl).dvd_prod_iff).1 h'
  rwa [(Nat.prime_dvd_prime_iff_eq hl (hp p hps)).1 hlp]

theorem lucas_list (n a : ℕ) (ps : List ℕ) (K : ℕ) (hd : n - 1 ∣ ps.prod ^ K) (hp : ∀ p ∈ ps, p.Prime)
    (h1 : (a : ZMod n) ^ (n - 1) = 1) (h2 : ∀ p ∈ ps, (a : ZMod n) ^ ((n - 1) / p) ≠ 1) : n.Prime := by
  refine lucas_primality n (a : ZMod n) h1 fun q hq hqd => h2 q ?_
  exact mem_of_dvd_prod_pow hq ps K hp (hqd.trans hd)

private theorem zmod_pow_eq_one_of_pow_mod_eq_one {n a e : ℕ} (h : a ^ e % n = 1) : (a : ZMod n) ^ e = 1 := by
  rw [← Nat.cast_pow, ← ZMod.natCast_mod, h, Nat.cast_one]

private theorem zmod_pow_ne_one_of_pow_mod_ne_one {n a e : ℕ} (hn : 1 < n) (h : a ^ e % n ≠ 1) : (a : ZMod n) ^ e ≠ 1 := by
  intro hc
  apply h
  have h2 := (ZMod.natCast_eq_natCast_iff' (a ^ e) 1 n).1 (by push_cast; exact hc)
  rwa [Nat.mod_eq_of_lt hn] at h2

private theorem pow_mod_of_two_pow_window {a n e e' r s : ℕ} (k w : ℕ) (h : a ^ e % n = r) (he : 2 ^ k * e + w = e')
    (hs : r ^ (2 ^ k) * a ^ w % n = s) : a ^ e' % n = s := by
  subst he hs h
  rw [pow_add, pow_mul', Nat.mul_mod, Nat.pow_mod (a ^ e) (2 ^ k) n]
  conv_rhs => rw [Nat.mul_mod]

private theorem residue_of_powMod {b e m r : Nat} (h : Nat.powMod b e m = r) :
    b ^ e % m = r := (Nat.powMod_def b e m).symm.trans h

private theorem pow_34_mod_413718278401_eq_one : 34 ^ (413718278401 - 1) % 413718278401 = 1 :=
  residue_of_powMod (by decide +kernel)

private theorem pow_34_div_2_mod_413718278401 : 34 ^ ((413718278401 - 1) / 2) % 413718278401 = 413718278400 :=
  residue_of_powMod (by decide +kernel)

private theorem pow_34_div_3_mod_413718278401 : 34 ^ ((413718278401 - 1) / 3) % 413718278401 = 89850750709 :=
  residue_of_powMod (by decide +kernel)

private theorem pow_34_div_5_mod_413718278401 : 34 ^ ((413718278401 - 1) / 5) % 413718278401 = 266539016536 :=
  residue_of_powMod (by decide +kernel)

private theorem pow_34_div_7_mod_413718278401 : 34 ^ ((413718278401 - 1) / 7) % 413718278401 = 309839479931 :=
  residue_of_powMod (by decide +kernel)

private theorem pow_34_div_571_mod_413718278401 : 34 ^ ((413718278401 - 1) / 571) % 413718278401 = 319448285034 :=
  residue_of_powMod (by decide +kernel)

private theorem pow_34_div_599_mod_413718278401 : 34 ^ ((413718278401 - 1) / 599) % 413718278401 = 112346021238 :=
  residue_of_powMod (by decide +kernel)

theorem gA_prime : Nat.Prime 413718278401 := by
  refine lucas_list 413718278401 34 [2, 3, 5, 7, 571, 599] 8 (by norm_num) ?_ (zmod_pow_eq_one_of_pow_mod_eq_one pow_34_mod_413718278401_eq_one) ?_
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> first  | norm_num
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    · exact zmod_pow_ne_one_of_pow_mod_ne_one (by norm_num) (by rw [pow_34_div_2_mod_413718278401]; decide)
    · exact zmod_pow_ne_one_of_pow_mod_ne_one (by norm_num) (by rw [pow_34_div_3_mod_413718278401]; decide)
    · exact zmod_pow_ne_one_of_pow_mod_ne_one (by norm_num) (by rw [pow_34_div_5_mod_413718278401]; decide)
    · exact zmod_pow_ne_one_of_pow_mod_ne_one (by norm_num) (by rw [pow_34_div_7_mod_413718278401]; decide)
    · exact zmod_pow_ne_one_of_pow_mod_ne_one (by norm_num) (by rw [pow_34_div_571_mod_413718278401]; decide)
    · exact zmod_pow_ne_one_of_pow_mod_ne_one (by norm_num) (by rw [pow_34_div_599_mod_413718278401]; decide)

private theorem pow_17_mod_603339156001_eq_one : 17 ^ (603339156001 - 1) % 603339156001 = 1 :=
  residue_of_powMod (by decide +kernel)

private theorem pow_17_div_2_mod_603339156001 : 17 ^ ((603339156001 - 1) / 2) % 603339156001 = 603339156000 :=
  residue_of_powMod (by decide +kernel)

private theorem pow_17_div_3_mod_603339156001 : 17 ^ ((603339156001 - 1) / 3) % 603339156001 = 365611846549 :=
  residue_of_powMod (by decide +kernel)

private theorem pow_17_div_5_mod_603339156001 : 17 ^ ((603339156001 - 1) / 5) % 603339156001 = 553231665472 :=
  residue_of_powMod (by decide +kernel)

private theorem pow_17_div_7_mod_603339156001 : 17 ^ ((603339156001 - 1) / 7) % 603339156001 = 477321853338 :=
  residue_of_powMod (by decide +kernel)

private theorem pow_17_div_571_mod_603339156001 : 17 ^ ((603339156001 - 1) / 571) % 603339156001 = 490793655739 :=
  residue_of_powMod (by decide +kernel)

private theorem pow_17_div_599_mod_603339156001 : 17 ^ ((603339156001 - 1) / 599) % 603339156001 = 511931551140 :=
  residue_of_powMod (by decide +kernel)

theorem gB_prime : Nat.Prime 603339156001 := by
  refine lucas_list 603339156001 17 [2, 3, 5, 7, 571, 599] 8 (by norm_num) ?_ (zmod_pow_eq_one_of_pow_mod_eq_one pow_17_mod_603339156001_eq_one) ?_
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> first  | norm_num
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    · exact zmod_pow_ne_one_of_pow_mod_ne_one (by norm_num) (by rw [pow_17_div_2_mod_603339156001]; decide)
    · exact zmod_pow_ne_one_of_pow_mod_ne_one (by norm_num) (by rw [pow_17_div_3_mod_603339156001]; decide)
    · exact zmod_pow_ne_one_of_pow_mod_ne_one (by norm_num) (by rw [pow_17_div_5_mod_603339156001]; decide)
    · exact zmod_pow_ne_one_of_pow_mod_ne_one (by norm_num) (by rw [pow_17_div_7_mod_603339156001]; decide)
    · exact zmod_pow_ne_one_of_pow_mod_ne_one (by norm_num) (by rw [pow_17_div_571_mod_603339156001]; decide)
    · exact zmod_pow_ne_one_of_pow_mod_ne_one (by norm_num) (by rw [pow_17_div_599_mod_603339156001]; decide)

private theorem pow_5_mod_large_prime_eq_one : 5 ^ (65794571027774832745588537266486439382601586586498771901135640963549130131839564588689999034983373394040350895271937 - 1) % 65794571027774832745588537266486439382601586586498771901135640963549130131839564588689999034983373394040350895271937 = 1 :=
  residue_of_powMod (by decide +kernel)

private theorem pow_5_div_2_mod_large_prime : 5 ^ ((65794571027774832745588537266486439382601586586498771901135640963549130131839564588689999034983373394040350895271937 - 1) / 2) % 65794571027774832745588537266486439382601586586498771901135640963549130131839564588689999034983373394040350895271937 = 65794571027774832745588537266486439382601586586498771901135640963549130131839564588689999034983373394040350895271936 :=
  residue_of_powMod (by decide +kernel)

private theorem pow_5_div_3_mod_large_prime : 5 ^ ((65794571027774832745588537266486439382601586586498771901135640963549130131839564588689999034983373394040350895271937 - 1) / 3) % 65794571027774832745588537266486439382601586586498771901135640963549130131839564588689999034983373394040350895271937 = 29509020182834794054055448241224306530711236629070958796785690203864100238794752395734553678655453420725957366984012 :=
  residue_of_powMod (by decide +kernel)

private theorem pow_5_div_571_mod_large_prime : 5 ^ ((65794571027774832745588537266486439382601586586498771901135640963549130131839564588689999034983373394040350895271937 - 1) / 571) % 65794571027774832745588537266486439382601586586498771901135640963549130131839564588689999034983373394040350895271937 = 7934320002768819286461108990260177925300080178601486319791509231030835586007543700012788172220637604788975808929610 :=
  residue_of_powMod (by decide +kernel)

private theorem pow_5_div_599_mod_large_prime : 5 ^ ((65794571027774832745588537266486439382601586586498771901135640963549130131839564588689999034983373394040350895271937 - 1) / 599) % 65794571027774832745588537266486439382601586586498771901135640963549130131839564588689999034983373394040350895271937 = 24233938224649648911732636907835869352432775843492941817614740309514131976760512423872779323164828855282365339575638 :=
  residue_of_powMod (by decide +kernel)

private theorem pow_5_div_413718278401_mod_large_prime : 5 ^ ((65794571027774832745588537266486439382601586586498771901135640963549130131839564588689999034983373394040350895271937 - 1) / 413718278401) % 65794571027774832745588537266486439382601586586498771901135640963549130131839564588689999034983373394040350895271937 = 33163391371698712807634046670708244078112533286827586181310971904178486489410920652603700297172713734367235080255888 :=
  residue_of_powMod (by decide +kernel)

private theorem pow_5_div_603339156001_mod_large_prime : 5 ^ ((65794571027774832745588537266486439382601586586498771901135640963549130131839564588689999034983373394040350895271937 - 1) / 603339156001) % 65794571027774832745588537266486439382601586586498771901135640963549130131839564588689999034983373394040350895271937 = 23095646587523677525525390906745661934228658823014094468462573805912009773578693855792857389218857894840490160291284 :=
  residue_of_powMod (by decide +kernel)

theorem prime_large : Nat.Prime 65794571027774832745588537266486439382601586586498771901135640963549130131839564588689999034983373394040350895271937 := by
  refine lucas_list 65794571027774832745588537266486439382601586586498771901135640963549130131839564588689999034983373394040350895271937 5 [2, 3, 571, 599, 413718278401, 603339156001] 12 (by norm_num) ?_ (zmod_pow_eq_one_of_pow_mod_eq_one pow_5_mod_large_prime_eq_one) ?_
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact gA_prime | exact gB_prime | norm_num
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    · exact zmod_pow_ne_one_of_pow_mod_ne_one (by norm_num) (by rw [pow_5_div_2_mod_large_prime]; decide)
    · exact zmod_pow_ne_one_of_pow_mod_ne_one (by norm_num) (by rw [pow_5_div_3_mod_large_prime]; decide)
    · exact zmod_pow_ne_one_of_pow_mod_ne_one (by norm_num) (by rw [pow_5_div_571_mod_large_prime]; decide)
    · exact zmod_pow_ne_one_of_pow_mod_ne_one (by norm_num) (by rw [pow_5_div_599_mod_large_prime]; decide)
    · exact zmod_pow_ne_one_of_pow_mod_ne_one (by norm_num) (by rw [pow_5_div_413718278401_mod_large_prime]; decide)
    · exact zmod_pow_ne_one_of_pow_mod_ne_one (by norm_num) (by rw [pow_5_div_603339156001_mod_large_prime]; decide)

def prodPowSubOne (g : ℕ) : ℕ := ((List.range 9).map fun i => g ^ (i + 1) - 1).prod

theorem exc_dvd {g d l : ℕ} (hg : 1 ≤ g) (h1 : 1 ≤ d) (h9 : d ≤ 9) (h : Formalism.CyclotomicNorms.Exc g d l) : l ∣ prodPowSubOne g := by
  have hv : padicValNat l (g ^ d - 1) ≠ 0 := by
    intro h0
    have := h.2
    rw [h0, mul_zero, pow_zero] at this
    have := Nat.one_le_pow d g hg
    omega
  refine ((dvd_pow_self l hv).trans (_root_.Dvd.intro_left _ (_root_.Nat.divMaxPow_mul_pow_padicValNat _ _))).trans (List.dvd_prod ?_)
  exact List.mem_map.mpr ⟨d - 1, List.mem_range.mpr (by omega), by rw [Nat.sub_add_cancel h1]⟩

theorem not_exc {g d l k : ℕ} (h1 : ¬ l ^ (k + 1) ∣ g ^ d - 1) (h2 : l ^ (4 * k) ≤ g ^ d) :
    ¬ Formalism.CyclotomicNorms.Exc g d l := by
  rintro ⟨hl, h⟩
  have hv : padicValNat l (g ^ d - 1) ≤ k := by
    by_contra hc
    exact h1 ((pow_dvd_pow l (by omega)).trans (_root_.Dvd.intro_left _ (_root_.Nat.divMaxPow_mul_pow_padicValNat _ _)))
  have := Nat.pow_le_pow_right hl.pos (Nat.mul_le_mul_left 4 hv)
  omega

theorem BB_disj0 : Disjoint (Formalism.CyclotomicNorms.BB 9 413718278401) (Formalism.CyclotomicNorms.BB 9 603339156001) := by
  rw [Set.disjoint_left]
  rintro l (rfl | ⟨d, h1, h9, h⟩) (h' | ⟨d', h1', h9', h'⟩)
  · exact absurd (Set.mem_singleton_iff.mp h') (by norm_num)
  · exact absurd (exc_dvd (by norm_num) h1' h9' h') (by decide +kernel)
  · rw [Set.mem_singleton_iff.mp h'] at h
    exact absurd (exc_dvd (by norm_num) h1 h9 h) (by decide +kernel)
  · have hg : Nat.gcd (prodPowSubOne 413718278401) (prodPowSubOne 603339156001) ∣ [2, 3, 5, 7, 11, 13, 37, 571, 599].prod ^ 52 := by decide +kernel
    have hm := mem_of_dvd_prod_pow h.1 _ _ (by decide +kernel)
      ((Nat.dvd_gcd (exc_dvd (by norm_num) h1 h9 h) (exc_dvd (by norm_num) h1' h9' h')).trans hg)
    have key : ∀ l ∈ [2, 3, 5, 7, 11, 13, 37, 571, 599], ∀ d ∈ List.range 10, 1 ≤ d → ∃ k ∈ List.range 20,
        ¬ l ^ (k + 1) ∣ 413718278401 ^ d - 1 ∧ l ^ (4 * k) ≤ 413718278401 ^ d := by decide +kernel
    obtain ⟨k, -, hk1, hk2⟩ := key l hm d (List.mem_range.mpr (by omega)) h1
    exact not_exc hk1 hk2 h

end Formalism.BasicNotions.Examples₂
