module

public import Green64.Library.Weights.Part113
public import Green64.Library.Weights.Part111
public import Green64.Library.Weights.Part112
public import Green64.Library.Correlation.PhysicalSharedFreeCarrierSum

@[expose] public section

/-!
# Correlation / Part073

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## MarkedPhysicalPGate -/

section

open Filter Topology
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64FullPhysicalE Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000

/-- Literal original physical cap failures at DR*n and DR*(n+s), multiplied
by BOTH actual marked factors and BOTH natural divisor-square envelopes.
The single inverse DR is the original shared harmonic normalization. -/
def parityMarkedPhysicalPcapHarmonicEnvelope434
    (Pall : Finset ℕ) (L : ℝ) (DR : ℕ) (W : ℕ→ℝ)
    (X : ℝ) (s : ℤ) (psi : ℝ→ℂ) (M : ℕ) : ℝ :=
  (DR:ℝ)⁻¹ * ∑ n∈Finset.Ioc 0 M,
    ‖psi ((n:ℝ)/X)‖/(n:ℝ)*parityMarkedPairWeight434 W s n*
      ((if ⌊Real.exp ((1/44:ℝ)*L)⌋₊ < sourceOriginalPPrimePart Pall (DR*n) then 1 else 0)+
       (if ⌊Real.exp ((1/44:ℝ)*L)⌋₊ < sourceOriginalPPrimePart Pall (DR*((n:ℤ)+s).toNat) then 1 else 0))

/-- The original physical cap failure implies the quotient half-tail;
no invariance of the two caps is asserted. -/
theorem parity_original_physical_cap_failure_half_tail434
    (Pall : Finset ℕ) (L : ℝ) (DR n : ℕ)
    (hDR : 0<DR) (hn : 0<n) (hSupport : DR.primeFactors⊆Pall)
    (hSmall : (DR:ℝ)≤Real.exp ((1/88:ℝ)*L))
    (hBad : ⌊Real.exp ((1/44:ℝ)*L)⌋₊ < sourceOriginalPPrimePart Pall (DR*n)) :
    ⌊Real.exp ((1/88:ℝ)*L)⌋₊ < sourceOriginalPPrimePart Pall n := by
  have hh := b575_failed_physical_Pcap_has_stripped_tail Pall DR n (1/44) L
    hDR hn hSupport
    (by norm_num only [show (1/44:ℝ)/2=1/88 by norm_num];exact hSmall) hBad
  norm_num only [show (1/44:ℝ)/2=1/88 by norm_num] at hh
  exact hh

/-- Exact finite harmonic transfer of a two-endpoint product tail. All
physical cap tests remain literal; only the proved failure-to-half-tail
implication is used to dominate them. -/
theorem parity_marked_physical_Pcap_harmonic_bound434
    (Pall : Finset ℕ) (L X K Cpsi F : ℝ)
    (hL : 0<L) (hX : 1≤X) (hK : 0≤K) (hF : 0≤F)
    (DR : ℕ) (hDR : 0<DR) (hSupport : DR.primeFactors⊆Pall)
    (hSmall : (DR:ℝ)≤Real.exp ((1/88:ℝ)*L))
    (W : ℕ→ℝ) (hW : ∀ n,0≤W n)
    (s : ℤ) (hs : |(s:ℝ)|≤X/128)
    (hTail : ∀ (S : Finset ℕ) (s' : ℤ), S⊆Finset.Ioc 0 ⌈65*X⌉₊ →
      (∀ n∈S,0<(n:ℤ)+s' ∧ (n:ℤ)+s'≤(⌈65*X⌉₊:ℤ)) →
      (∑ n∈S.filter (fun n : ℕ=>⌊Real.exp ((1/88:ℝ)*L)⌋₊ < sourceOriginalPPrimePart Pall n),
        parityMarkedPairWeight434 W s' n)+
      (∑ n∈S.filter (fun n : ℕ=>⌊Real.exp ((1/88:ℝ)*L)⌋₊ < sourceOriginalPPrimePart Pall ((n:ℤ)+s').toNat),
        parityMarkedPairWeight434 W s' n) ≤ 2*(⌈65*X⌉₊:ℝ)*F)
    (psi : ℝ→ℂ)
    (hSupp : ∀ t,psi t≠0 → t∈Set.Icc (1/64:ℝ) 64)
    (hPsi : ∀ t,‖psi t‖≤K*L^Cpsi) (M : ℕ) :
    parityMarkedPhysicalPcapHarmonicEnvelope434 Pall L DR W X s psi M ≤
      (128*66:ℝ)*(DR:ℝ)⁻¹*K*L^Cpsi*F := by
  classical
  let S := (Finset.Ioc 0 M).filter (fun n : ℕ=>psi ((n:ℝ)/X)≠0)
  let Y := ⌈65*X⌉₊
  let B : ℝ := 64*K*L^Cpsi/X
  let a : ℕ→ℝ := fun n : ℕ=>‖psi ((n:ℝ)/X)‖/(n:ℝ)
  let pair : ℕ→ℝ := parityMarkedPairWeight434 W s
  let phy : ℕ→ℝ := fun n : ℕ=>if ⌊Real.exp ((1/44:ℝ)*L)⌋₊ < sourceOriginalPPrimePart Pall (DR*n) then 1 else 0
  let half : ℕ→ℝ := fun n : ℕ=>if ⌊Real.exp ((1/88:ℝ)*L)⌋₊ < sourceOriginalPPrimePart Pall n then 1 else 0
  have hXp : 0<X := by linarith
  have hB : 0≤B := by dsimp [B];positivity
  have hp0 (n : ℕ) : 0≤pair n := parity_marked_pair_weight_nonneg434 W hW s n
  have hgeom (n : ℕ) (hn : n∈S) := parity_harmonic_cutoff_shift_support434 X hXp s hs psi hSupp n
    (Finset.mem_filter.mp hn).2
  have hSub : S⊆Finset.Ioc 0 Y := by
    intro n hn
    exact Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1).1,(hgeom n hn).2.2.1⟩
  have hShift : ∀ n∈S,0<(n:ℤ)+s ∧ (n:ℤ)+s≤(Y:ℤ) :=
    fun n hn=>⟨(hgeom n hn).1,(hgeom n hn).2.1⟩
  have hcoef (n : ℕ) (hn : n∈S) : a n≤B := by
    have hnpos : 0<(n:ℝ) := by exact_mod_cast (Finset.mem_Ioc.mp (hSub hn)).1
    apply (div_le_iff₀ hnpos).mpr
    calc
      _ ≤ K*L^Cpsi := hPsi _
      _ = B*(X/64) := by dsimp [B];field_simp
      _ ≤ B*(n:ℝ) := mul_le_mul_of_nonneg_left (hgeom n hn).2.2.2 hB
  have hflag (n : ℕ) (hn : 0<n) : phy n≤half n := by
    by_cases h : ⌊Real.exp ((1/44:ℝ)*L)⌋₊ < sourceOriginalPPrimePart Pall (DR*n)
    · have hh := parity_original_physical_cap_failure_half_tail434 Pall L DR n hDR hn hSupport hSmall h
      simp only [phy,half,if_pos h,if_pos hh,le_refl]
    · dsimp only [phy]
      rw [if_neg h]
      dsimp only [half]
      split_ifs <;> norm_num
  have hrestrict : (∑ n∈Finset.Ioc 0 M,a n*pair n*(phy n+phy ((n:ℤ)+s).toNat)) =
      ∑ n∈S,a n*pair n*(phy n+phy ((n:ℤ)+s).toNat) := by
    dsimp only [S]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hz : psi ((n:ℝ)/X)=0 <;> simp [a,hz]
  have hflagsum : (∑ n∈S,B*pair n*(half n+half ((n:ℤ)+s).toNat)) =
      B*((∑ n∈S.filter (fun n : ℕ=>⌊Real.exp ((1/88:ℝ)*L)⌋₊ < sourceOriginalPPrimePart Pall n),pair n)+
      (∑ n∈S.filter (fun n : ℕ=>⌊Real.exp ((1/88:ℝ)*L)⌋₊ < sourceOriginalPPrimePart Pall ((n:ℤ)+s).toNat),pair n)) := by
    simp only [Finset.sum_filter,mul_add,Finset.mul_sum,Finset.sum_add_distrib]
    congr 1
    · apply Finset.sum_congr rfl
      intro n hn
      by_cases h : ⌊Real.exp ((1/88:ℝ)*L)⌋₊ < sourceOriginalPPrimePart Pall n <;> simp [half,h]
    · apply Finset.sum_congr rfl
      intro n hn
      by_cases h : ⌊Real.exp ((1/88:ℝ)*L)⌋₊ < sourceOriginalPPrimePart Pall ((n:ℤ)+s).toNat <;> simp [half,h]
  have hsum : (∑ n∈Finset.Ioc 0 M,a n*pair n*(phy n+phy ((n:ℤ)+s).toNat)) ≤B*(2*(Y:ℝ)*F) := by
    calc
      _ = ∑ n∈S,a n*pair n*(phy n+phy ((n:ℤ)+s).toNat) := hrestrict
      _ ≤ ∑ n∈S,B*pair n*(half n+half ((n:ℤ)+s).toNat) := by
        apply Finset.sum_le_sum
        intro n hn
        have hnpos := (Finset.mem_Ioc.mp (hSub hn)).1
        have hnp : 0<((n:ℤ)+s).toNat := by have hh:=(hgeom n hn).1;omega
        have hf0 : 0≤phy n+phy ((n:ℤ)+s).toNat := by dsimp [phy];split_ifs <;> norm_num
        calc
          _ ≤ B*pair n*(phy n+phy ((n:ℤ)+s).toNat) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hcoef n hn) (hp0 n)) hf0
          _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add (hflag n hnpos) (hflag _ hnp)) (mul_nonneg hB (hp0 n))
      _ = _ := hflagsum
      _ ≤ _ := mul_le_mul_of_nonneg_left (hTail S s hSub hShift) hB
  have hY : (Y:ℝ)≤66*X := by
    have hh := Nat.ceil_lt_add_one (show 0≤65*X by positivity)
    dsimp only [Y]
    linarith
  have hlen : 2*(Y:ℝ)*F ≤ 2*(66*X)*F :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hY (by norm_num)) hF
  have hDRR : (DR:ℝ)≠0 := by exact_mod_cast hDR.ne'
  change (DR:ℝ)⁻¹*(∑ n∈Finset.Ioc 0 M,a n*pair n*(phy n+phy ((n:ℤ)+s).toNat)) ≤ _
  calc
    _ ≤ (DR:ℝ)⁻¹*(B*(2*(Y:ℝ)*F)) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ (DR:ℝ)⁻¹*(B*(2*(66*X)*F)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlen hB) (by positivity)
    _ = _ := by dsimp [B];field_simp;ring

/-- Full actual higher-mark product Pcap envelope at every logarithmic
precision. The original physical caps use sigma=1/44, the proved tail uses
sigma/2=1/88, and no cap invariance or assumed marked product estimate occurs. -/
theorem parity_eventually_actual_marked_physical_Pcap_harmonic434
    (J : ℕ) (Cpsi A : ℝ) :
    ∀ᶠ L : ℝ in atTop, Real.exp 2≤L ∧
      (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
      ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
        (m : ℕ) (hmJ : m≤J)
        (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
        (DR : ℕ) (X K : ℝ) (s : ℤ) (psi : ℝ→ℂ) (M : ℕ),
        0<DR → DR.primeFactors⊆Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L) →
        (DR:ℝ)≤Real.exp ((1/88:ℝ)*L) → 1≤X → 0≤K →
        |(s:ℝ)|≤X/128 → Real.log (⌈65*X⌉₊:ℝ)≤2*L →
        (∀ t,psi t≠0 → t∈Set.Icc (1/64:ℝ) 64) →
        (∀ t,‖psi t‖≤K*L^Cpsi) →
        parityMarkedPhysicalPcapHarmonicEnvelope434
          (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) L DR
          (parityActualFullMarkedWeight434 L hS J m hmJ nu) X s psi M ≤
            ((128*66:ℝ)*(3:ℝ)^128)*(DR:ℝ)⁻¹*K*L^(-A) := by
  filter_upwards [parity_eventually_actual_marked_both_half_tails434 J (A+Cpsi)] with L hTail
  refine ⟨hTail.1,hTail.2.1,?_⟩
  intro hS m hmJ nu DR X K s psi M hDR hSupport hSmall hX hK hs hLog hSupp hPsi
  have hLp : 0<L := (Real.exp_pos _).trans_le hTail.1
  have hY : 1≤⌈65*X⌉₊ := by
    have hh : 65*X≤(⌈65*X⌉₊:ℝ) := Nat.le_ceil _
    have hh' : (1:ℝ)≤(⌈65*X⌉₊:ℝ) := by linarith
    exact_mod_cast hh'
  have ht := parity_marked_physical_Pcap_harmonic_bound434
    (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L))
    L X K Cpsi ((3:ℝ)^128*L^(-(A+Cpsi))) hLp hX hK (by positivity)
    DR hDR hSupport hSmall (parityActualFullMarkedWeight434 L hS J m hmJ nu)
    (fun n : ℕ=>norm_nonneg _) s hs
    (by
      intro S s' hSub hShift
      simpa only [mul_assoc] using hTail.2.2 hS m hmJ nu ⌈65*X⌉₊ S s' hY hLog hSub hShift)
    psi hSupp hPsi M
  have hp : L^Cpsi*L^(-(A+Cpsi))=L^(-A) := by
    rw [←Real.rpow_add hLp]
    congr 1
    ring
  calc
    _ ≤ (128*66:ℝ)*(DR:ℝ)⁻¹*K*L^Cpsi*((3:ℝ)^128*L^(-(A+Cpsi))) := ht
    _ = ((128*66:ℝ)*(3:ℝ)^128)*(DR:ℝ)⁻¹*K*(L^Cpsi*L^(-(A+Cpsi))) := by ring
    _ = _ := by rw [hp]
end Green64Analytic.SourceBlockSieve

end

end

/-! ## ActualMarkedFramePGate -/

section

open Filter Topology
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64FullPhysicalE Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000

/-- The full marked product error for BOTH original physical caps on every
actual Parity frame. The actual shared factor and auxiliary factor supply all
size/support/geometry premises; precision is fixed before the eventual L.
This estimates the literal cap-loss envelope, not an insertion identity for
the independently defined uncapped physical harmonic functional. -/
theorem parity_eventually_actual_frame_marked_Pcap_saving434
    (J : ℕ) (CZ Ck Cpsi A : ℝ) (hCZ : 0 ≤ CZ) :
    ∀ᶠ L : ℝ in atTop, 1 < L ∧
      (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
    ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
      (m : ℕ) (hmJ : m ≤ J)
      (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
      (Nu : Type) [Fintype Nu]
      (patterns : Nu → SourcePattern (sourceNativeOriginalBigType434 20 L) J m)
      (positions : Finset ℤ) (x : B654ActualParityState434 L hS J positions)
      (f : MemoryPrimitiveEFrame (SG:=SourceNativeMemorySG434 20 L hS)
        (SourceNativeMemoryBP434 20 L) J 1 m patterns)
      (Z : ℝ), Real.exp L*L^(-CZ) ≤ Z → Z ≤ Real.exp L*L^CZ →
    ∀ (k : ℤ), |(k:ℝ)| ≤ L^Ck →
    ∀ (K : ℝ), 0 ≤ K →
    ∀ (psi : ℝ → ℂ),
      (∀ t, psi t ≠ 0 → t ∈ Set.Icc (1/64:ℝ) 64) →
      (∀ t, ‖psi t‖ ≤ K*L^Cpsi) →
    ∀ M : ℕ,
      let DR := parityFrameSharedD434
        (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
        (SourceNativeMemoryBP434 20 L) (fun _ p => p.val)
        J 1 m patterns x.val.2 f
      let DC := parityFrameAuxD434 (SourceNativeMemoryBP434 20 L)
        (fun _ p => p.val) J 1 m patterns f
      parityMarkedPhysicalPcapHarmonicEnvelope434
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) L DR
        (parityActualFullMarkedWeight434 L hS J m hmJ nu)
        (Z*(DC:ℝ)) (2*k*(DC:ℤ)) psi M ≤
        ((128*66:ℝ)*(3:ℝ)^128)*(DR:ℝ)⁻¹*K*L^(-A) := by
  filter_upwards [parity_eventually_harmonic_scale_budget434 CZ Ck hCZ,
    parity_eventually_actual_frame_shared_half_Pcap434 J,
    b651_eventually_parity_window_sqrt434 J 0 (by norm_num),
    parity_eventually_actual_marked_physical_Pcap_harmonic434 J Cpsi A,
    eventually_gt_atTop (1:ℝ)] with L hBudget hSmall hW hErr hL
  refine ⟨hL,hErr.2.1,?_⟩
  intro hS m hmJ nu Nu inst patterns positions x f Z hZlo hZhi k hk K hK psi hSupp hPsi M
  dsimp only
  let DR := parityFrameSharedD434
    (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
    (SourceNativeMemoryBP434 20 L) (fun _ p => p.val)
    J 1 m patterns x.val.2 f
  let DC := parityFrameAuxD434 (SourceNativeMemoryBP434 20 L)
    (fun _ p => p.val) J 1 m patterns f
  have hDR : 0 < DR := parity_frame_shared_D_pos434
    (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
    (SourceNativeMemoryBP434 20 L) (fun _ p => p.val)
    J 1 m patterns x.val.2 f
  have hDC : 0 < DC := parity_frame_aux_D_pos434
    (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J 1 m patterns f
  have hSupport : DR.primeFactors ⊆ Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L) := by
    change DR.primeFactors ⊆ sourceNativeOriginalG434 20 L
    exact parity_actual_frame_shared_P_support434 L hL hS J m patterns positions x f
  have hDRsmall : (DR:ℝ) ≤ Real.exp ((1/88:ℝ)*L) :=
    hSmall.2 hS m Nu patterns positions x f
  have hDChi : (DC:ℝ) ≤ Real.exp (Real.sqrt L) :=
    (parity_actual_frame_aux_window434 L hW.1 hS J m patterns x.val.2 f).trans hW.2
  have hb := hBudget.2 Z hZlo hZhi DC hDC hDChi k hk
  exact hErr.2.2 hS m hmJ nu DR (Z*(DC:ℝ)) K (2*k*(DC:ℤ)) psi M
    hDR hSupport hDRsmall hb.1 hK hb.2.1 hb.2.2 hSupp hPsi
end Green64Analytic.SourceBlockSieve

end

end

/-! ## PhysicalSharedFreeCapDomination -/

section

open Filter Topology
open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 12000

namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD Green64FullPhysicalE

/-- Sum of BOTH literal original physical cap-failure indicators. It
majorizes their union without replacing either DR*w argument. -/
def parityOriginalPhysicalPcapFlags434 (L : ℝ) (d w wp : ℕ) : ℝ :=
  (if ⌊Real.exp ((1/44:ℝ)*L)⌋₊ < sourceOriginalPPrimePart (sourceNativeOriginalG434 20 L) (d*w) then 1 else 0) +
  (if ⌊Real.exp ((1/44:ℝ)*L)⌋₊ < sourceOriginalPPrimePart (sourceNativeOriginalG434 20 L) (d*wp) then 1 else 0)

theorem parity_original_physical_Pcap_flags_nonneg434 (L : ℝ) (d w wp : ℕ) :
    0≤parityOriginalPhysicalPcapFlags434 L d w wp := by
  unfold parityOriginalPhysicalPcapFlags434
  split_ifs <;> norm_num

/-- Exact union loss is dominated by the two original endpoint flags.
No tail estimate or cap invariance is used. -/
theorem parity_original_physical_Pcap_loss_norm434 (L : ℝ) (d w wp : ℕ) :
    ‖1-parityOriginalPhysicalPairPcap434 L (d*w) (d*wp)‖ ≤
      parityOriginalPhysicalPcapFlags434 L d w wp := by
  rw [parity_original_pair_Pcap_complement434]
  unfold parityOriginalPhysicalPcapFlags434
  rw [show L/44=(1/44:ℝ)*L by ring]
  split_ifs <;> norm_num at * <;> omega

/-- The literal canonical physical-slice envelope at actual r20 data.
SharedMass includes the original single DR inverse. The Q^4 xi^-2 cap
is the proved bound on BOTH inverse cell masses of the original kernel. -/
def parityActualPhysicalMarkedEnvelope434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m≤J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    (Q : ℕ) (xi : ℝ)
    (s : ∀ g : B645ActualGroup434 L hS,
      sourceOriginalProbeSharedSlots434 J 1 m hmJ
        (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu) g → ℕ)
    (w wp : ℕ) : ℝ :=
  (1/2:ℝ)^(-2*((J+1)*Fintype.card (B645ActualGroup434 L hS):ℝ)) *
    sourceB574SharedMass434 (J+1)
      (sourceOriginalProbeSharedSlots434 J 1 m hmJ
        (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu))
      (Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L)) s *
    ((Q:ℝ)^4*(xi⁻¹)^2) *
    parityActualFullMarkedWeight434 L hS J m hmJ nu w *
    parityActualFullMarkedWeight434 L hS J m hmJ nu wp

/-- The actual full physical kernel has this marked envelope on EVERY
shared array in the real carrier. Prime support, mass nonnegativity and
disjoint full bands are derived from actual r20 definitions. No clean,
collision-free, kernel-bound or physical-envelope premise is assumed. -/
theorem parity_actual_B574_physical_marked_bound434
    (L : ℝ) (hL : 1<L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m≤J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    (Q : ℕ) (h xi : ℝ) (hh : 0<h) (hxi : 0<xi)
    (aux : ParityActualProbeAux434 L J m hmJ nu)
    (s : ∀ g : B645ActualGroup434 L hS,
      sourceOriginalProbeSharedSlots434 J 1 m hmJ
        (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu) g → ℕ)
    (hs : ∀ g i,s g i∈b645ActualBand434 L hS g) (w wp : ℕ) :
    ‖parityActualB574Physical434 L hS J m hmJ nu Q h xi aux s w wp‖ ≤
      parityActualPhysicalMarkedEnvelope434 L hS J m hmJ nu Q xi s w wp := by
  have hV (g : B645ActualGroup434 L hS) :
      0≤Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L) g := by
    rw [parity_actual_full_mass_exact434]
    exact Finset.sum_nonneg (fun p hp => by positivity)
  simpa only [parityActualB574Physical434,parityActualPhysicalMarkedEnvelope434,
    parityActualFullMarkedWeight434,Nat.cast_one] using
    source_B574_canonical_physical_slice_bound434 J 1 m hmJ
      (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu)
      Q h h xi (b645ActualBand434 L hS)
      (Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L))
      (parityFullProbeAuxLift434 (SourceNativeMemorySG434 20 L hS) m nu
        (sourceOriginalProbeMemoryAuxValues434 (sourceNativeOriginalTb434 20 L) J m hmJ nu aux))
      (1/2) w wp s hh hh hxi (by norm_num) (by norm_num) hV
      (fun g p hp => (parity_actual_full_band_prime_floor434 L hL.le hS g p hp).1)
      hs (parity_actual_full_band_disjoint434 L hL hS)

/-- Native arithmetic stripping gives a pointwise norm bound even before
removing the original finite source seed. No support or seed identity is
assumed; the zero seed branch is simply nonnegative on the right. -/
theorem parity_actual_shared_arithmetic_norm_le434
    (L : ℝ) (hL : 1<L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (M : ℕ) (E : B645ActualGroup434 L hS → Finset (Fin M))
    (s : ∀ g,E g → ℕ) (hs : ∀ g i,s g i∈b645ActualBand434 L hS g)
    (rho xi3 Z : ℝ) (lo hi : ℕ) (F G : PrimeSlotCore)
    (tw : Bool) (psi : ℝ → ℂ) (c w wp : ℕ)
    (hc : 0<c) (hw : 0<w) (hwp : 0<wp) :
    ‖parityHarmonicSharedArithmetic434 L (-xi3) Z lo hi F G
        (-(rho+xi3)) (-rho) tw 0 psi (sourceB574SharedDilation434 M E s) c w wp‖ ≤
    ‖parityHarmonicStrippedArithmetic434 L (-xi3) Z F G
        (-(rho+xi3)) (-rho) tw psi c w wp‖ := by
  rw [parity_actual_labelled_shared_arithmetic434 L hL hS M E s hs rho xi3 Z lo hi F G
    tw psi c w wp hc hw hwp]
  split_ifs
  · exact le_rfl
  · simpa only [norm_zero] using norm_nonneg
      (parityHarmonicStrippedArithmetic434 L (-xi3) Z F G (-(rho+xi3)) (-rho) tw psi c w wp)

/-- One literal comparison cap-loss integrand from the frozen capped
aggregate, at actual balanced Parity frequencies and v=0. This definition
retains the original seed, physical caps, auxiliary probability and full
physical slice. The signed shift guard is left to the surrounding sum. -/
def parityActualPhysicalComparisonCapLossTerm434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m≤J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    (Q : ℕ) (h xi rho xi3 Z : ℝ) (lo hi : ℕ)
    (F G : PrimeSlotCore) (tw : Bool) (psi : ℝ → ℂ)
    (aux : ParityActualProbeAux434 L J m hmJ nu)
    (s : ∀ g : B645ActualGroup434 L hS,
      sourceOriginalProbeSharedSlots434 J 1 m hmJ
        (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu) g → ℕ)
    (w wp : ℕ) : ℂ :=
  let d := sourceB574SharedDilation434 (J+1)
    (sourceOriginalProbeSharedSlots434 J 1 m hmJ
      (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu)) s
  let c := parityActualProbeAuxD434 L J m hmJ nu aux
  (1-parityOriginalPhysicalPairPcap434 L (d*w) (d*wp)) *
    parityHarmonicSharedArithmetic434 L (-xi3) Z lo hi F G (-(rho+xi3)) (-rho) tw 0 psi d c w wp *
    (sourceAuxMass (SourceNativeMemoryBP434 20 L) (fun _ p=>p.val) J m
      (sourceNativeOriginalVbig434 20 L) (sourceOriginalProbeMemoryPattern434 J m hmJ nu) aux : ℂ) *
    parityActualB574Physical434 L hS J m hmJ nu Q h xi aux s w wp

/-- Genuine pointwise cap-loss domination. The full physical slice bound
and common arithmetic stripping are proved, while BOTH original cap
flags, auxiliary probability and both marked endpoint factors remain. -/
theorem parity_actual_comparison_cap_loss_marked434
    (L : ℝ) (hL : 1<L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m≤J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    (Q : ℕ) (h xi rho xi3 Z : ℝ) (hh : 0<h) (hxi : 0<xi) (lo hi : ℕ)
    (F G : PrimeSlotCore) (tw : Bool) (psi : ℝ → ℂ)
    (aux : ParityActualProbeAux434 L J m hmJ nu)
    (s : ∀ g : B645ActualGroup434 L hS,
      sourceOriginalProbeSharedSlots434 J 1 m hmJ
        (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu) g → ℕ)
    (hs : ∀ g i,s g i∈b645ActualBand434 L hS g)
    (w wp : ℕ) (hw : 0<w) (hwp : 0<wp) :
    let d := sourceB574SharedDilation434 (J+1)
      (sourceOriginalProbeSharedSlots434 J 1 m hmJ
        (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu)) s
    let c := parityActualProbeAuxD434 L J m hmJ nu aux
    ‖parityActualPhysicalComparisonCapLossTerm434 L hS J m hmJ nu Q h xi rho xi3 Z lo hi F G tw psi aux s w wp‖ ≤
      parityOriginalPhysicalPcapFlags434 L d w wp *
      ‖parityHarmonicStrippedArithmetic434 L (-xi3) Z F G (-(rho+xi3)) (-rho) tw psi c w wp‖ *
      ‖(sourceAuxMass (SourceNativeMemoryBP434 20 L) (fun _ p=>p.val) J m
        (sourceNativeOriginalVbig434 20 L) (sourceOriginalProbeMemoryPattern434 J m hmJ nu) aux : ℂ)‖ *
      parityActualPhysicalMarkedEnvelope434 L hS J m hmJ nu Q xi s w wp := by
  dsimp only
  let d := sourceB574SharedDilation434 (J+1)
    (sourceOriginalProbeSharedSlots434 J 1 m hmJ
      (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu)) s
  let c := parityActualProbeAuxD434 L J m hmJ nu aux
  have hc := parity_actual_probe_aux_positive434 L hS J m hmJ nu aux
  have hA := parity_actual_shared_arithmetic_norm_le434 L hL hS (J+1)
    (sourceOriginalProbeSharedSlots434 J 1 m hmJ
      (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu)) s hs
    rho xi3 Z lo hi F G tw psi c w wp hc hw hwp
  have hB := parity_actual_B574_physical_marked_bound434 L hL hS J m hmJ nu Q h xi hh hxi aux s hs w wp
  have hC := parity_original_physical_Pcap_loss_norm434 L d w wp
  have hC0 := parity_original_physical_Pcap_flags_nonneg434 L d w wp
  unfold parityActualPhysicalComparisonCapLossTerm434
  dsimp only
  simp only [norm_mul]
  apply mul_le_mul
    (mul_le_mul_of_nonneg_right (mul_le_mul hC hA (norm_nonneg _) hC0) (norm_nonneg _))
    hB (norm_nonneg _)
  exact mul_nonneg (mul_nonneg hC0 (norm_nonneg _)) (norm_nonneg _)

/-- The pointwise cap-loss bound for the TRUE B633 actual Parity endpoint
cores. Both divisor-square bounds are derived before choosing the shared
array and auxiliary draw. No arbitrary core norm or physical slice bound
is an assumption. The threshold and all original physical caps stay literal. -/
theorem parity_eventually_actual_B633_comparison_cap_loss434
    (S beta gamma : ℝ) (hSfine : 0<S) (hbeta : 0<beta) (hgamma : 0<gamma) :
    ∀ᶠ L : ℝ in atTop, 1<L ∧
      ∀ (prime : Bool) (l u : ℕ), Real.exp (beta*L)≤(l:ℝ) →
      ∀ (r e : ℕ), 1≤ r → ∀ (b : Fin (e+1)) (slot : Fin r)
        (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r e L) b slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels r (sourceActualSortedScales r e L) b slot).length → ℝ)
        (K : Finset ℕ) (q : ℕ) (chi : DirichletCharacter ℂ q) (s0 s1 : ℝ),
        let F := sourceNativePrimeCore r e L b slot δ ξ K
          (b629ActualFineAlpha434 prime L S gamma l u) q chi s0 s1
        ∀ xi1 xi2 rho sigma : ℝ,
        let E := b633ParityEFirstCore434 F.alpha F.residual q chi F.lo F.hi xi2 rho sigma
        let G := b633ParitySecondCore434 F.alpha F.residual q chi F.lo F.hi xi1 rho sigma
        ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (J m : ℕ) (hmJ : m≤J)
          (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
          (Q : ℕ) (h xi xi3 Z : ℝ), 0<h → 0<xi →
        ∀ (lo hi : ℕ) (tw : Bool) (psi : ℝ→ℂ)
          (aux : ParityActualProbeAux434 L J m hmJ nu)
          (s : ∀ g : B645ActualGroup434 L hS,
            sourceOriginalProbeSharedSlots434 J 1 m hmJ
              (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu) g → ℕ),
          (∀ g i,s g i∈b645ActualBand434 L hS g) →
        ∀ (w wp : ℕ), 0<w → 0<wp →
          let d := sourceB574SharedDilation434 (J+1)
            (sourceOriginalProbeSharedSlots434 J 1 m hmJ
              (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu)) s
          let c := parityActualProbeAuxD434 L J m hmJ nu aux
          ‖parityActualPhysicalComparisonCapLossTerm434 L hS J m hmJ nu Q h xi rho xi3 Z lo hi E G tw psi aux s w wp‖ ≤
            parityOriginalPhysicalPcapFlags434 L d w wp *
            ((w:ℝ)⁻¹*(w.divisors.card:ℝ)^2*(wp.divisors.card:ℝ)^2*‖psi ((w:ℝ)/(Z*(c:ℝ)))‖) *
            ‖(sourceAuxMass (SourceNativeMemoryBP434 20 L) (fun _ p=>p.val) J m
              (sourceNativeOriginalVbig434 20 L) (sourceOriginalProbeMemoryPattern434 J m hmJ nu) aux : ℂ)‖ *
            parityActualPhysicalMarkedEnvelope434 L hS J m hmJ nu Q xi s w wp := by
  filter_upwards [parity_eventually_actual_B633_stripped_tau434 S beta gamma hSfine hbeta hgamma,
    eventually_gt_atTop (1:ℝ)] with L hCore hL
  refine ⟨hL,?_⟩
  intro prime l u hlow r e hr b slot δ ξ K q chi s0 s1
  dsimp only
  intro xi1 xi2 rho sigma hS J m hmJ nu Q h xi xi3 Z hh hxi lo hi tw psi aux s hs w wp hw hwp
  let F := sourceNativePrimeCore r e L b slot δ ξ K
    (b629ActualFineAlpha434 prime L S gamma l u) q chi s0 s1
  let E := b633ParityEFirstCore434 F.alpha F.residual q chi F.lo F.hi xi2 rho sigma
  let G := b633ParitySecondCore434 F.alpha F.residual q chi F.lo F.hi xi1 rho sigma
  let d := sourceB574SharedDilation434 (J+1)
    (sourceOriginalProbeSharedSlots434 J 1 m hmJ
      (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu)) s
  let c := parityActualProbeAuxD434 L J m hmJ nu aux
  have hMain := parity_actual_comparison_cap_loss_marked434 L hL hS J m hmJ nu Q h xi rho xi3 Z hh hxi
    lo hi E G tw psi aux s hs w wp hw hwp
  dsimp only at hMain
  have hTau := hCore.2 prime l u hlow r e hr b slot δ ξ K q chi s0 s1 xi1 xi2 rho sigma
    xi3 Z tw psi c w wp hw hwp
  have hB := parity_actual_B574_physical_marked_bound434 L hL hS J m hmJ nu Q h xi hh hxi aux s hs w wp
  have hB0 := (norm_nonneg _).trans hB
  have hC0 := parity_original_physical_Pcap_flags_nonneg434 L d w wp
  exact hMain.trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hTau hC0) (norm_nonneg _)) hB0)
end Green64Analytic.Parity

end

end

