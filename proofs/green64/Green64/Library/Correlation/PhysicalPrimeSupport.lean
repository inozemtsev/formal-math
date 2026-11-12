module

public import Green64.Library.Weights.Part085
public import Green64.Library.Analysis.Estimates.Part011
public import Green64.Library.Weights.Part075
public import Mathlib

@[expose] public section

/-!
# Correlation / PhysicalPrimeSupport

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceNativePhysicalPrimeSupport -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64FullPhysicalE Green64SmallHaar
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 8500000

/-- A genuine prime dividing a finite product must divide one of the
actual factors, including repeated factors. No squarefree assumption. -/
private theorem original_physical_prime_dvd_finset_prod434
    {I : Type} [DecidableEq I]
    (S : Finset I) (f : I → ℕ) (p : ℕ) (hp : p.Prime)
    (h : p ∣ ∏ i ∈ S, f i) :
    ∃ i ∈ S, p ∣ f i := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp only [Finset.prod_empty] at h
      exact (hp.not_dvd_one h).elim
  | @insert i S hi ih =>
      rw [Finset.prod_insert hi] at h
      rcases (hp.dvd_mul.mp h) with h1 | hrest
      · exact ⟨i, Finset.mem_insert_self _ _, h1⟩
      · obtain ⟨j,hj,hjdiv⟩ := ih hrest
        exact ⟨j, Finset.mem_insert_of_mem hj, hjdiv⟩

/-- EVERY prime factor of the TRUE SOURCE03 Fock/seen physical
divisor D=original SMALL shared × BIG shared × BIG free auxiliary
is in the original S/Ts/Tb P union, INCLUDING repeated valuations
and both independent endpoint group permutations.

This follows from the literal sourceOrientedPhysicalD definition and
source prime bands, not an auxiliary or comparator factor surrogate. -/
theorem source_native_original_FULL_PHYSICAL_D_prime_support434
    (r : ℕ) (L : ℝ)
    (hS : (sourceNativeOriginalSmallIndices434 r L).Nonempty)
    (J ell m : ℕ)
    (cap : sourceNativeOriginalBigType434 r L → ℕ)
    (pat : SourcePattern (sourceNativeOriginalBigType434 r L) J m)
    (aux : SourceBigAux (SourceNativeMemoryBP434 r L) J m pat)
    (x : FullPhysicalState
      (SourceNativeMemorySP434 r L hS) (fun _ p => p.val)
      (SourceNativeMemoryBP434 r L) (fun _ p => p.val)
      (J+ell) cap)
    (bs : BigGroupPerm (BG:=sourceNativeOriginalBigType434 r L)
      (J+ell))
    (ss : GroupPermFamily
      (G:=SourceNativeMemorySG434 r L hS) (J+ell))
    (p : ℕ) (hp : p.Prime)
    (hdiv : p ∣ sourceOrientedPhysicalD
      (SourceNativeMemorySP434 r L hS) (fun _ p => p.val)
      (SourceNativeMemoryBP434 r L) (fun _ p => p.val)
      J ell m cap pat aux x bs ss) :
    p ∈ sourceNativeOriginalG434 r L := by
  classical
  let SG := SourceNativeMemorySG434 r L hS
  let SP := SourceNativeMemorySP434 r L hS
  let BG := sourceNativeOriginalBigType434 r L
  let BP := SourceNativeMemoryBP434 r L
  let dsmall := sourceOriginalPhysicalSourceSMALLFactor434
    SP (fun _ p => p.val) BP (fun _ p => p.val) J ell cap x ss
  let dbig := sourceOriginalPhysicalSourceBIGFactor434
    SP (fun _ p => p.val) BP (fun _ p => p.val)
    J ell m cap pat aux x bs
  have hEq : sourceOrientedPhysicalD
      SP (fun _ p => p.val) BP (fun _ p => p.val)
      J ell m cap pat aux x bs ss = dsmall*dbig :=
    source_original_ACTUAL_PHYSICAL_D_SMALL_TIMES_BIG434
      SP (fun _ p => p.val) BP (fun _ p => p.val)
      J ell m cap pat aux x bs ss
  rw [hEq] at hdiv
  rcases (hp.dvd_mul.mp hdiv) with hSdiv | hBdiv
  · unfold dsmall sourceOriginalPhysicalSourceSMALLFactor434 at hSdiv
    obtain ⟨g,hg,hgdiv⟩ :=
      original_physical_prime_dvd_finset_prod434 (Finset.univ : Finset SG)
        (fun g => ∏ j ∈ sourceSmallShared J ell g,
          ((marks (fun (q : SP g) => q.val) (J+ell) (x.1 g)
            (ss g j)).val)) p hp hSdiv
    obtain ⟨j,hj,hjdiv⟩ :=
      original_physical_prime_dvd_finset_prod434
        (sourceSmallShared J ell g)
        (fun j => (marks (fun (q : SP g) => q.val) (J+ell) (x.1 g)
          (ss g j)).val) p hp hgdiv
    let chosen : SP g := marks (fun (q : SP g) => q.val)
      (J+ell) (x.1 g) (ss g j)
    have hChosen : (chosen.val).Prime := by
      cases g with
      | none =>
        exact (source_native_original_S_prime_range434 r L hS
          chosen.val chosen.property).1
      | some i =>
        exact (source_native_original_Ts_prime_range434 r L hS i
          chosen.val chosen.property).1
    have hEqP : p=chosen.val :=
      (Nat.prime_dvd_prime_iff_eq hp hChosen).mp hjdiv
    subst p
    cases g with
    | none =>
      exact Finset.mem_biUnion.mpr
        ⟨sourceNativeOriginalSGroup434 r L hS,
          Finset.mem_univ _, chosen.property⟩
    | some i =>
      exact Finset.mem_biUnion.mpr
        ⟨sourceNativeOriginalTsGroup434 r L hS i,
          Finset.mem_univ _, chosen.property⟩
  · unfold dbig sourceOriginalPhysicalSourceBIGFactor434 at hBdiv
    obtain ⟨g,hg,hgdiv⟩ :=
      original_physical_prime_dvd_finset_prod434
        (Finset.univ : Finset BG)
        (fun g =>
          (∏ i ∈ sourceBigShared J ell m pat g,
            ((x.2 g).1 (bs g i)).val) *
          (∏ j : ↥(pat.free g), (aux g j).val)) p hp hBdiv
    rcases (hp.dvd_mul.mp hgdiv) with hSh | hAux
    · obtain ⟨i,hi,hidiv⟩ :=
        original_physical_prime_dvd_finset_prod434
          (sourceBigShared J ell m pat g)
          (fun i => ((x.2 g).1 (bs g i)).val)
          p hp hSh
      let q : BP g := (x.2 g).1 (bs g i)
      have hPrime : q.val.Prime :=
        (source_native_original_Tb_prime_range434 r L g
          q.val q.property).1
      have he : p=q.val :=
        (Nat.prime_dvd_prime_iff_eq hp hPrime).mp hidiv
      subst p
      exact Finset.mem_biUnion.mpr
        ⟨sourceNativeOriginalBigToAll434 r L g,
          Finset.mem_univ _, q.property⟩
    · obtain ⟨j,hj,hjdiv⟩ :=
        original_physical_prime_dvd_finset_prod434
          (Finset.univ : Finset ↥(pat.free g))
          (fun j => (aux g j).val) p hp hAux
      let q : BP g := aux g j
      have hPrime : q.val.Prime :=
        (source_native_original_Tb_prime_range434 r L g
          q.val q.property).1
      have he : p=q.val :=
        (Nat.prime_dvd_prime_iff_eq hp hPrime).mp hjdiv
      subst p
      exact Finset.mem_biUnion.mpr
        ⟨sourceNativeOriginalBigToAll434 r L g,
          Finset.mem_univ _, q.property⟩
end Green64Analytic.SourceBlockSieve

end

end

