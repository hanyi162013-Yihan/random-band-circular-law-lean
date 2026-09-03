/- Source snapshot: upstream-sources/high-band-lsv-2609-01295/RadialLedger.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.NeighborPath
import Vendor.PlanarSmallBall

/-! Exact cancellation of radial net cardinalities against row probabilities. -/

open scoped BigOperators

namespace HighBandLSV.RadialLedger

theorem prod_const_pow {I : Type*} (s : Finset I) (a : Real) (m : I → Nat) :
    (∏ i ∈ s, a ^ m i) = a ^ (∑ i ∈ s, m i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih, pow_add]

theorem prod_fixed_pow {I : Type*} (s : Finset I) (a : I → Real) (r : Nat) :
    (∏ i ∈ s, a i ^ r) = (∏ i ∈ s, a i) ^ r := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih, mul_pow]

theorem weight_pow_le {x : Real} {r m : Nat}
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hr : r ≤ m) : x ^ m ≤ x ^ r := by
  have hm : m = r + (m - r) := (Nat.add_sub_of_le hr).symm
  calc
    x ^ m = x ^ r * x ^ (m - r) := by
      calc
        x ^ m = x ^ (r + (m - r)) := congrArg (fun t : Nat => x ^ t) hm
        _ = x ^ r * x ^ (m - r) := pow_add x r (m - r)
    _ ≤ x ^ r := by
      have hpow : x ^ (m - r) ≤ 1 := pow_le_one₀ hx hx1
      nlinarith [pow_nonneg hx r]

theorem net_weight_bound {J N r : Nat} {A h : Real}
    (m : Fin J → Nat) (w : Fin J → Real)
    (hA : 0 ≤ A) (hh : 0 < h) (hw : ∀ j, 0 < w j)
    (hw1 : ∀ j, w j ≤ 1) (hm : ∀ j, r ≤ m j) (hsum : ∑ j, m j = N) :
    (∏ j, (A * w j / h ^ 2) ^ m j) ≤
      (A / h ^ 2) ^ N * (∏ j, w j) ^ r := by
  have hterm : ∀ j, (A * w j / h ^ 2) ^ m j ≤
      (A / h ^ 2) ^ m j * w j ^ r := by
    intro j
    rw [show A * w j / h ^ 2 = (A / h ^ 2) * w j by ring, mul_pow]
    exact mul_le_mul_of_nonneg_left
      (weight_pow_le (hw j).le (hw1 j) (hm j)) (by positivity)
  calc
    (∏ j, (A * w j / h ^ 2) ^ m j) ≤
        ∏ j, ((A / h ^ 2) ^ m j * w j ^ r) := by
      apply Finset.prod_le_prod
      · intro j _
        exact pow_nonneg (div_nonneg (mul_nonneg hA (hw j).le) (sq_nonneg h)) _
      · intro j _
        exact hterm j
    _ = (∏ j, (A / h ^ 2) ^ m j) * ∏ j, w j ^ r :=
      Finset.prod_mul_distrib
    _ = (A / h ^ 2) ^ N * (∏ j, w j) ^ r := by
      rw [prod_const_pow, hsum, prod_fixed_pow]

theorem row_product {J r : Nat} (B : Real) (w : Fin J → Real) :
    (∏ j, (B / w j) ^ r) = (B ^ J / (∏ j, w j)) ^ r := by
  rw [prod_fixed_pow, Finset.prod_div_distrib]
  simp

theorem net_row_cancellation {J N r : Nat} {k l : Fin J}
    (p : NeighborPath.Path k l) (m : Fin J → Nat) (w : Fin J → Real)
    {A B h : Real} (hA : 0 ≤ A) (hB : 0 ≤ B) (hh : 0 < h)
    (hw : ∀ j, 0 < w j) (hw1 : ∀ j, w j ≤ 1)
    (hm : ∀ j, r ≤ m j) (hsum : ∑ j, m j = N) :
    (∏ j, (A * w j / h ^ 2) ^ m j) *
        (∏ j, (B / w (NeighborPath.next p.vertices j)) ^ r) ≤
      (A / h ^ 2) ^ N * B ^ (r * J) * (w k / w l) ^ r := by
  have hrow : 0 ≤ ∏ j, (B / w (NeighborPath.next p.vertices j)) ^ r := by
    apply Finset.prod_nonneg
    intro j _
    exact pow_nonneg (div_nonneg hB (hw (NeighborPath.next p.vertices j)).le) r
  calc
    (∏ j, (A * w j / h ^ 2) ^ m j) *
        (∏ j, (B / w (NeighborPath.next p.vertices j)) ^ r) ≤
      ((A / h ^ 2) ^ N * (∏ j, w j) ^ r) *
        (∏ j, (B / w (NeighborPath.next p.vertices j)) ^ r) :=
      mul_le_mul_of_nonneg_right
        (net_weight_bound m w hA hh hw hw1 hm hsum) hrow
    _ = (A / h ^ 2) ^ N * B ^ (r * J) *
        ((∏ j, w j) / (∏ j, w (NeighborPath.next p.vertices j))) ^ r := by
      rw [row_product]
      simp only [div_pow, pow_mul, Nat.mul_comm J r]
      ring
    _ = (A / h ^ 2) ^ N * B ^ (r * J) * (w k / w l) ^ r := by
      rw [NeighborPath.inverse_product_ratio p w hw]

theorem endpoint_ratio_bound {J : Nat} {wSmall wLarge delta : Real}
    (hJ : 0 < J) (hlarge : 0 < wLarge)
    (hsmall : wSmall ≤ delta ^ 2) (hheavy : 1 / (4 * (J : Real)) ≤ wLarge) :
    wSmall / wLarge ≤ 4 * (J : Real) * delta ^ 2 := by
  have hJr : 0 < (J : Real) := Nat.cast_pos.mpr hJ
  have hmul : 1 ≤ wLarge * (4 * (J : Real)) :=
    (div_le_iff₀ (by positivity : 0 < 4 * (J : Real))).mp hheavy
  apply (div_le_iff₀ hlarge).2
  have hdelta : 0 ≤ delta ^ 2 := sq_nonneg delta
  nlinarith [mul_le_mul_of_nonneg_right hmul hdelta]

theorem radial_to_endpoint_bound {J N r : Nat} {k l : Fin J}
    (p : NeighborPath.Path k l) (m : Fin J → Nat) (w : Fin J → Real)
    {A B h delta : Real} (hJ : 0 < J)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hh : 0 < h)
    (hw : ∀ j, 0 < w j) (hw1 : ∀ j, w j ≤ 1)
    (hm : ∀ j, r ≤ m j) (hsum : ∑ j, m j = N)
    (hsmall : w k ≤ delta ^ 2) (hheavy : 1 / (4 * (J : Real)) ≤ w l) :
    (∏ j, (A * w j / h ^ 2) ^ m j) *
        (∏ j, (B / w (NeighborPath.next p.vertices j)) ^ r) ≤
      (A / h ^ 2) ^ N * B ^ (r * J) * (4 * (J : Real) * delta ^ 2) ^ r := by
  apply (net_row_cancellation p m w hA hB hh hw hw1 hm hsum).trans
  apply mul_le_mul_of_nonneg_left
  · exact pow_le_pow_left₀ (div_nonneg (hw k).le (hw l).le)
      (endpoint_ratio_bound hJ (hw l) hsmall hheavy) r
  · positivity

theorem endpoint_factor_le {J : Nat} {A K delta : Real}
    (hA : 4 ≤ A) (hK : 0 ≤ K) (hd : 0 ≤ delta) (hd1 : delta ≤ 1) :
    4 * (J : Real) * delta ^ 2 ≤ A * (K + 1) * J * delta := by
  have hAK : 4 ≤ A * (K + 1) := by nlinarith
  have hdsq : delta ^ 2 ≤ delta := by nlinarith
  calc
    4 * (J : Real) * delta ^ 2 ≤ 4 * (J : Real) * delta := by gcongr
    _ ≤ A * (K + 1) * J * delta := by gcongr

end HighBandLSV.RadialLedger

#print axioms HighBandLSV.RadialLedger.net_row_cancellation
#print axioms HighBandLSV.RadialLedger.radial_to_endpoint_bound

