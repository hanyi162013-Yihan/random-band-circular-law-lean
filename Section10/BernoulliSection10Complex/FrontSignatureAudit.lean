import BernoulliSection10Complex.Front

/-! Type-level regression checks for the actual complex model, followed by
the public signatures. This checks theorem hypotheses separately from the
kernel-axiom allowlist; a conditional theorem can pass an axiom audit. -/

open MeasureTheory

namespace BernoulliSection10Complex

example (W s : ℕ) :
    IntervalRows W s = (Fin (s * W) → Fin (3 * W) → ℂ) := rfl

example (W s : ℕ) (μ : Measure ℂ) :
    intervalRowsLaw W s μ =
      Measure.pi (fun _ : Fin (s * W) =>
        Measure.pi (fun _ : Fin (3 * W) => μ)) := rfl

example (W : ℕ) (x : PhysicalRowAtoms W) (b : Fin 3) (c : Fin W) :
    normalizedPhysicalAtom x b c =
      (blockNormalization W : ℂ) * x (BernoulliSection10.physicalAtomIndex b c) := rfl

set_option pp.fullNames true in
#print IsPlanarDensityAtom

#check @planar_lemma_10_2_rho
#check @planar_lemma_10_2_resampling
#check @planar_corollary_10_3
#check @planar_lemma_10_5
#check @planar_intervalMaxHodgeEnvelope_memLp_two
#check @planar_intervalMaxHodgeEnvelope_lintegral_le_W_log_eW
#check @planar_proposition_10_7_periodic_seam
#check @planar_proposition_10_8_integrated_endpoint_comparison
#check @planar_proposition_10_9
#check @planar_proposition_10_10_packet_reset
#check @planar_physicalPacketResetLoss_integral_le
#check @planar_intervalPressure_reset_increment
#check @planar_cyclicPressure_normalized_L1_bound
#check @density_ring_energy_limit_of_second_moment

end BernoulliSection10Complex
