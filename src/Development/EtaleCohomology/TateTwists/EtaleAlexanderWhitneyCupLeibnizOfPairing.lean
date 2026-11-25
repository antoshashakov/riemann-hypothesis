module

public import Development.EtaleCohomology.TateTwists.EtaleAlexanderWhitneyCupLeibniz
public import Development.EtaleCohomology.KummerTheory.CupAWCutEv
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.TypeStar
import Development.EtaleCohomology.KummerTheory.CupAWCut

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open LateralTheory.KummerTheory.AW

namespace LateralTheory.EtaleFoundations.AWLeib
variable {R : Type} [CommRing R]

theorem bd_map {E : Spc} {U : Scheme.{0}} {G G' : Type*} [AddCommGroup G] [AddCommGroup G'] (φ : G →+ G')
    (f : ∀ p : ℕ, Sx E p U → G) (p : ℕ) (y : Sx E p U) : φ (bd f p y) = bd (fun q z => φ (f q z)) p y := by
  cases p with
  | zero => simp [bd]
  | succ p => simp [bd, map_sum, map_zsmul]

theorem ev_delta_bd {E : Spc} {I : Cx R} {n m : ℤ} (hm : n + 1 = m) (α : Cochain ((chains R).obj E) I n) (p : ℕ)
    (s t : ℤ) (hs : -(p : ℤ) + n = s) (ht : -(p : ℤ) + m = t) (U : Scheme.{0}) (x : Sx E p U) :
    ev (R := R) (δ n m α) p t ht U x = Sec.map (I.d s t) (ev (R := R) α p s hs U x) +
      m.negOnePow • bd (fun q z => if hh : -(q : ℤ) + n = t then ev (R := R) α q t hh U z else 0) p x := by
  have ev_eq {k : ℤ} (a : Cochain ((chains R).obj E) I k) (q : ℕ) (j : ℤ)
      (h : -(q : ℤ) + k = j) (y : Sx E q U) :
      ev (R := R) a q j h U y = Sec.map ((chainsXIso R E q).inv ≫ a.v _ _ h) (freeGen R _ U y) := rfl
  cases p with
  | zero =>
    rw [ev_eq, δ_v n m hm α _ _ ht s 1 (by omega) (by simp),
      (isZero_pos E 1 one_pos).eq_of_tgt (((chains R).obj E).d _ 1) 0]
    simp only [zero_comp, smul_zero, add_zero, bd]
    rfl
  | succ p =>
    have hp : -(p : ℤ) + n = t := by omega
    rw [ev_eq, δ_v n m hm α _ _ ht s (-(p : ℤ)) (by omega) (by omega),
      Preadditive.comp_add, Linear.comp_units_smul, reassoc_of% (chains_d (R := R) E p),
      Preadditive.sum_comp]
    refine (sec_map_add _ _ _).trans ?_
    congr 1
    rw [Units.smul_def, Units.smul_def, sec_map_zsmul, sec_map_sum]
    congr 1
    simp only [bd, dite_eq_left hp]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Preadditive.zsmul_comp, sec_map_zsmul, ev_eq]
    congr 1
    exact congrArg (Sec.map ((chainsXIso R E p).inv ≫ α.v (-(p : ℤ)) t hp)) (map_freeGen (E.δ i) U x)

theorem mul_congr {I J K : Cx R} (μ : Pair I J K) (U : Scheme.{0}) {E : Spc} {n m : ℤ}
    (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m) (p q : ℕ) (y : Sx E p U) (z : Sx E q U)
    (s t w s' t' : ℤ) (h : s + t = w) (h' : s' + t' = w) (hs : -(p : ℤ) + n = s) (ht : -(q : ℤ) + m = t)
    (hs' : -(p : ℤ) + n = s') (ht' : -(q : ℤ) + m = t') :
    μ.mul U s t w h (ev (R := R) α p s hs U y) (ev (R := R) β q t ht U z) =
      μ.mul U s' t' w h' (ev (R := R) α p s' hs' U y) (ev (R := R) β q t' ht' U z) := by
  subst hs ht hs' ht'; rfl

theorem leib' {I J K : Cx R} (μ : Pair I J K) (U : Scheme.{0}) (s t w s' t' w' : ℤ) (h : s + t = w) (hs : s + 1 = s')
    (ht : t + 1 = t') (hw : w + 1 = w') (a : Sec (I.X s) U) (b : Sec (J.X t) U) :
    Sec.map (K.d w w') (μ.mul U s t w h a b) = μ.mul U s' t w' (by omega) (Sec.map (I.d s s') a) b +
      s.negOnePow • μ.mul U s t' w' (by omega) a (Sec.map (J.d t t') b) := by
  subst hs ht hw; exact μ.leibniz U s t w h a b

theorem mul_bd_left {I J K : Cx R} (μ : Pair I J K) {E : Spc} {U : Scheme.{0}} (s t w : ℤ) (h : s + t = w)
    (f : ∀ q : ℕ, Sx E q U → Sec (I.X s) U) (p : ℕ) (y : Sx E p U) (b : Sec (J.X t) U) :
    μ.mul U s t w h (bd f p y) b = bd (fun q z => μ.mul U s t w h (f q z) b) p y :=
  bd_map (((μ.mul U s t w h).flip b).toAddMonoidHom) f p y

theorem mul_bd_right {I J K : Cx R} (μ : Pair I J K) {E : Spc} {U : Scheme.{0}} (s t w : ℤ) (h : s + t = w)
    (f : ∀ q : ℕ, Sx E q U → Sec (J.X t) U) (p : ℕ) (y : Sx E p U) (a : Sec (I.X s) U) :
    μ.mul U s t w h a (bd f p y) = bd (fun q z => μ.mul U s t w h a (f q z)) p y :=
  bd_map ((μ.mul U s t w h a).toAddMonoidHom) f p y

theorem secmap_sum {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} {ι : Type*} (s : Finset ι) (f : ι → Sec F U) :
    Sec.map φ (∑ i ∈ s, f i) = ∑ i ∈ s, Sec.map φ (f i) := map_sum ((φ.hom.app (op U)).hom) f s

theorem secmap_zsmul {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (c : ℤ) (a : Sec F U) :
    Sec.map φ (c • a) = c • Sec.map φ a := map_zsmul ((φ.hom.app (op U)).hom) c a

def Fm {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m : ℤ} (α : Cochain ((chains R).obj E) I n)
    (β : Cochain ((chains R).obj E) J m) (U : Scheme.{0}) (w : ℤ) (p q : ℕ) (y : Sx E p U) (z : Sx E q U) :
    Sec (K.X w) U :=
  if hh : (-(p : ℤ) + n) + (-(q : ℤ) + m) = w then μ.mul U _ _ w hh (ev (R := R) α p _ rfl U y) (ev (R := R) β q _ rfl U z) else 0

theorem recombine {G : Type*} [AddCommGroup G] (X Y BF BF' BB BB' : G) (c s K c' P e1 e2 c2 e3 : ℤ) (hF : BF' = BF)
    (hB : BB' = BB) (h2 : c * s = e2 * c2) (h3 : K * c' = c * e1) (h4 : K * (c * P) = e2 * (c2 * e3)) :
    c • (X + s • Y) + K • (c' • BF + c • P • BB) = c • (X + e1 • BF') + e2 • c2 • (Y + e3 • BB') := by
  subst hF hB
  simp only [smul_add, smul_smul]
  rw [h2, h3, h4]
  abel

theorem sign_nat (p : ℕ) : ((-1 : ℤ) ^ p) = (((p : ℤ).negOnePow : ℤˣ) : ℤ) := by
  simp [Int.negOnePow_def]

end LateralTheory.EtaleFoundations.AWLeib


open LateralTheory.EtaleFoundations.AWLeib in
theorem LateralTheory.EtaleFoundations.etaleAlexanderWhitneyCup_leibniz_of_pairing : LateralTheory.EtaleFoundations.EtaleAlexanderWhitneyCupLeibniz :=
  _root_.LateralTheory.KummerTheory.AW.leibniz
