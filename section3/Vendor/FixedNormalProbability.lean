/- Source snapshot: upstream-sources/high-band-lsv-2609-01295/FixedNormalProbability.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.PlanarTensorization
import Vendor.RadialRawBound

/-! The fixed-index normal-space bound is constructed from the entry model. -/

open scoped BigOperators ENNReal
open MeasureTheory Set

noncomputable section

namespace HighBandLSV.FixedNormalProbability

local instance (p : Prop) : Decidable p := Classical.propDecidable p

theorem admissible_card_bound {J : Nat} {h delta : Real} (k l : Fin J)
    (hh : 0 < h) (hh1 : h ≤ 1) :
    let Q := {q : RadialNetAssembly.Labels J h // NormalNetEvents.admissible h delta k l q}
    (Fintype.card Q : Real) ≤ (3 / h) ^ J := by
  classical
  dsimp only
  have hcard : Fintype.card
      {q : RadialNetAssembly.Labels J h // NormalNetEvents.admissible h delta k l q} ≤
        Fintype.card (RadialNetAssembly.Labels J h) :=
    Fintype.card_le_of_injective (fun q => q.val) Subtype.val_injective
  have hcast : (Fintype.card
      {q : RadialNetAssembly.Labels J h // NormalNetEvents.admissible h delta k l q} : Real) ≤
        (PlanarNets.levelCount h : Real) ^ J := by
    exact_mod_cast (show Fintype.card
      {q : RadialNetAssembly.Labels J h // NormalNetEvents.admissible h delta k l q} ≤
        (PlanarNets.levelCount h) ^ J by
          simpa only [RadialNetAssembly.Labels, RadialNetAssembly.Label,
            Fintype.card_fun, Fintype.card_fin] using hcard)
  exact hcast.trans (pow_le_pow_left₀ (Nat.cast_nonneg _)
    (PlanarNets.levelCount_bound hh hh1) J)

theorem fixed_bad_probability {N J W r : Nat} {c C L A h K delta : Real}
    (m : PlanarBandModel N W c C L) (p : BlockGeometry.Partition N J)
    (hband : PathGeometry.LocalBand p W) (i : Fin N) (k l : Fin J) (z : Complex)
    (hN : 0 < N) (hJ : 0 < J) (hc : 0 < c) (hW : 0 < W) (hL : 0 ≤ L)
    (hA1 : 1 ≤ A) (hA : Real.pi * L / c ≤ A) (hh : 0 < h) (hh1 : h ≤ 1)
    (hK : 0 ≤ K) (hhd : h ≤ delta) (hsize : ∀ j, r + 1 ≤ (p.blocks j).card)
    (hmesh : h * Real.sqrt (J : Real) ≤ 1 / 2)
    (herror : (Real.sqrt (J : Real) * h) * K ≤ delta) :
    m.law ((fun omega => shifted (m.matrix omega) z) ⁻¹'
      NormalNetEvents.fixedBad p i k l K delta) ≤
        ENNReal.ofReal (RadialRawBound.fixedEnvelope N J r A W h delta) := by
  classical
  let net := RadialNetAssembly.chooseSystem p h hh
  let path := NeighborPath.between k l
  let rows := BlockGeometry.chooseRows p i r hsize
  let Q := {q : RadialNetAssembly.Labels J h // NormalNetEvents.admissible h delta k l q}
  let E : Q → Set (MatrixSample N) := fun q =>
    ⋃ v : net.Centers q.val, (fun omega => shifted (m.matrix omega) z) ⁻¹'
      NormalNetEvents.constraint (net.vector q.val v) rows.allRows delta
  let B := (25 / h ^ 2) ^ N * (A * (N : Real) * W * delta ^ 2) ^ (r * J) *
    (4 * (J : Real) * delta ^ 2) ^ r
  have hB : 0 ≤ B := by
    have hA0 : 0 ≤ A := zero_le_one.trans hA1
    dsimp [B]
    positivity
  have hE : ∀ q : Q, m.law (E q) ≤ ENNReal.ofReal B := by
    intro q
    exact PlanarTensorization.center_union_endpoint_bound m p hband path net q.val rows z
      hN hJ hc hW hL hA1 hA hh hh1 hhd
      (fun j => (Nat.le_succ r).trans (hsize j)) q.property
  have hcover := NormalNetEvents.fixedBad_subset_net_union p net i k l rows
    hJ hh hK hhd hmesh herror
  have hsubset : (fun omega => shifted (m.matrix omega) z) ⁻¹'
      NormalNetEvents.fixedBad p i k l K delta ⊆ ⋃ q : Q, E q := by
    intro omega homega
    have hmem := hcover homega
    obtain ⟨q, hq⟩ := mem_iUnion.mp hmem
    obtain ⟨v, hv⟩ := mem_iUnion.mp hq
    exact mem_iUnion.mpr ⟨q, mem_iUnion.mpr ⟨v, hv⟩⟩
  calc
    m.law ((fun omega => shifted (m.matrix omega) z) ⁻¹'
        NormalNetEvents.fixedBad p i k l K delta) ≤ m.law (⋃ q : Q, E q) :=
      measure_mono hsubset
    _ ≤ ENNReal.ofReal ((3 / h) ^ J * B) :=
      FiniteProbability.finite_union_of_card_bound m.law E hB
        (admissible_card_bound k l hh hh1) hE
    _ = ENNReal.ofReal (RadialRawBound.fixedEnvelope N J r A W h delta) := by
      congr 1
      dsimp [B, RadialRawBound.fixedEnvelope]
      ring

theorem bad_normal_probability {N J W r : Nat} {c C L A h K delta : Real}
    (m : PlanarBandModel N W c C L) (p : BlockGeometry.Partition N J)
    (hband : PathGeometry.LocalBand p W) (z : Complex)
    (hN : 0 < N) (hJ : 0 < J) (hc : 0 < c) (hW : 0 < W) (hL : 0 ≤ L)
    (hA1 : 1 ≤ A) (hA : Real.pi * L / c ≤ A) (hh : 0 < h) (hh1 : h ≤ 1)
    (hK : 0 ≤ K) (hhd : h ≤ delta) (hsize : ∀ j, r + 1 ≤ (p.blocks j).card)
    (hmesh : h * Real.sqrt (J : Real) ≤ 1 / 2)
    (herror : (Real.sqrt (J : Real) * h) * K ≤ delta) :
    m.law ((fun omega => shifted (m.matrix omega) z) ⁻¹'
      (NormalNetEvents.columnCap K \ NormalNetEvents.normalSpread p delta)) ≤
        ENNReal.ofReal ((N : Real) * J * J * RadialRawBound.fixedEnvelope N J r A W h delta) := by
  classical
  let Q := Fin N × Fin J × Fin J
  let E : Q → Set (MatrixSample N) := fun q =>
    (fun omega => shifted (m.matrix omega) z) ⁻¹'
      NormalNetEvents.fixedBad p q.1 q.2.1 q.2.2 K delta
  have hcover := NormalNetEvents.normal_cover p hJ (K := K) (hh.trans_le hhd)
  have hsubset : (fun omega => shifted (m.matrix omega) z) ⁻¹'
      (NormalNetEvents.columnCap K \ NormalNetEvents.normalSpread p delta) ⊆ ⋃ q : Q, E q := by
    intro omega homega
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover homega)
    obtain ⟨k, hk⟩ := mem_iUnion.mp hi
    obtain ⟨l, hl⟩ := mem_iUnion.mp hk
    exact mem_iUnion.mpr ⟨(i, k, l), hl⟩
  have hE : ∀ q : Q, m.law (E q) ≤
      ENNReal.ofReal (RadialRawBound.fixedEnvelope N J r A W h delta) := by
    intro q
    exact fixed_bad_probability m p hband q.1 q.2.1 q.2.2 z
      hN hJ hc hW hL hA1 hA hh hh1 hK hhd hsize hmesh herror
  apply (measure_mono hsubset).trans
  have hbound := FiniteProbability.finite_union m.law E hE
  convert hbound using 1
  congr 1
  simp only [Q, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
  ring

end HighBandLSV.FixedNormalProbability

#print axioms HighBandLSV.FixedNormalProbability.fixed_bad_probability
#print axioms HighBandLSV.FixedNormalProbability.bad_normal_probability

