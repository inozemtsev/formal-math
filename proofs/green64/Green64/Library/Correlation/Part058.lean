module

public import Green64.Library.Correlation.PhysicalPrimeSupport
public import Mathlib
public import Green64.Library.Weights.Part085
public import Green64.Library.Weights.Part048
public import Green64.Library.Weights.Part073
public import Green64.Library.Correlation.MemoryActualDomain
public import Green64.Library.Weights.Part024
public import Green64.Library.Weights.Part045
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Tactic
public import Green64.Library.Weights.Part042
public import Green64.Library.Weights.Part044
public import Green64.Library.Correlation.Part033
public import Green64.Library.Weights.Part017
public import Green64.Library.Weights.Part057
public import Green64.Library.Weights.Part082

@[expose] public section

/-!
# Correlation / Part058

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceNativePhysicalDPrimeFactorList -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64FullPhysicalE Green64SmallHaar
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 9500000

/-- The genuine original full S/Ts/Tb source physical divisor D on
the true Fock state is ALWAYS positive: every original labelled
SMALL, BIG shared and BIG free auxiliary atom is a prime, so no
zero source divisor can silently enter the character modulus. -/
theorem source_native_original_FULL_PHYSICAL_D_pos434
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
      (G:=SourceNativeMemorySG434 r L hS) (J+ell)) :
    0 < sourceOrientedPhysicalD
      (SourceNativeMemorySP434 r L hS) (fun _ p => p.val)
      (SourceNativeMemoryBP434 r L) (fun _ p => p.val)
      J ell m cap pat aux x bs ss := by
  classical
  let SG := SourceNativeMemorySG434 r L hS
  let SP := SourceNativeMemorySP434 r L hS
  let BG := sourceNativeOriginalBigType434 r L
  let BP := SourceNativeMemoryBP434 r L
  rw [source_original_ACTUAL_PHYSICAL_D_SMALL_TIMES_BIG434]
  apply mul_pos
  · unfold sourceOriginalPhysicalSourceSMALLFactor434
    apply Finset.prod_pos
    intro g hg
    apply Finset.prod_pos
    intro i hi
    let selected : SP g := marks (fun (q : SP g) => q.val)
      (J+ell) (x.1 g) (ss g i)
    change 0 < selected.val
    cases g with
    | none =>
      exact (source_native_original_S_prime_range434 r L hS
        selected.val selected.property).1.pos
    | some g =>
      exact (source_native_original_Ts_prime_range434 r L hS
        g selected.val selected.property).1.pos
  · unfold sourceOriginalPhysicalSourceBIGFactor434
    apply Finset.prod_pos
    intro g hg
    apply mul_pos
    · apply Finset.prod_pos
      intro i hi
      exact (source_native_original_Tb_prime_range434 r L g
        ((x.2 g).1 (bs g i)).val
        ((x.2 g).1 (bs g i)).property).1.pos
    · apply Finset.prod_pos
      intro j hj
      exact (source_native_original_Tb_prime_range434 r L g
        (aux g j).val (aux g j).property).1.pos

/-- Use the standard CANONICAL prime-factor multiset of the actual
original physical D, NOT a speculative labelled divisor list.
Positivity supplies exact product equality, and the previous true
physical P prime support theorem verifies every factor lies in
the unmodified S/Ts/Tb union. Multiplicities are retained because
primeFactorsList is a LIST, not a Finset. -/
theorem source_native_original_FULL_PHYSICAL_D_prime_factor_list434
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
      (G:=SourceNativeMemorySG434 r L hS) (J+ell)) :
    let D := sourceOrientedPhysicalD
      (SourceNativeMemorySP434 r L hS) (fun _ p => p.val)
      (SourceNativeMemoryBP434 r L) (fun _ p => p.val)
      J ell m cap pat aux x bs ss
    (D.primeFactorsList.prod = D) ∧
    (∀ p ∈ D.primeFactorsList, p ∈ sourceNativeOriginalG434 r L) := by
  classical
  let D := sourceOrientedPhysicalD
      (SourceNativeMemorySP434 r L hS) (fun _ p => p.val)
      (SourceNativeMemoryBP434 r L) (fun _ p => p.val)
      J ell m cap pat aux x bs ss
  have hpD : 0 < D :=
    source_native_original_FULL_PHYSICAL_D_pos434
      r L hS J ell m cap pat aux x bs ss
  have hD0 : D ≠ 0 := Nat.ne_of_gt hpD
  constructor
  · exact Nat.prod_primeFactorsList hD0
  · intro p hp
    have hprime := (Nat.mem_primeFactorsList hD0).mp hp
    exact source_native_original_FULL_PHYSICAL_D_prime_support434
      r L hS J ell m cap pat aux x bs ss p hprime.1 hprime.2
end Green64Analytic.SourceBlockSieve

end

end

/-! ## SourceNativeR6ActualFullFockLegal -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- A complete and ACTUALLY LEGAL entry of the ORIGINAL SOURCE03
physical E_i finite operator at original r=6 cofinal scales,
with true S/Ts SMALL Haar torus states, real Tb BIG prime labels,
independently sampled BIG free auxiliaries, zero OLD Fock state,
full permuted active endpoints, signed k=2, and exact
sourcePhysicalLegal source D/signed step.

The true physical source prime p_g and auxiliary q_g come from
each original dyadic P group (two distinct primes guaranteed by
uniform reciprocal harmonic mass), so the source auxiliary is
NOT an invented dummy label. The pattern is genuinely J=1,m=1
with one actual free BIG slot in every BIG group.
All original BIG legal tests and both endpoint auxiliary bans
hold for the constructed full source state and choice.

The theorem proves finite support of the TRUE full physical
operator is NONEMPTY, not that the actual operator coefficient
or its signed Fourier/Type II mean-square estimate is nonzero.
The input K, Haar phases and terminal vacuum are NOT replaced. -/
theorem eventually_source_native_r6_TRUE_FULL_FOCK_legal_nonempty434 :
    ∀ᶠ N : ℕ in atTop,
      1 ≤ N ∧
      let L := sourceNativeR6CofinalL434 N;
      let hS := source_native_r6_cofinal_SMALL_nonempty434 N;
      let pat := source_native_actual_J1_m1_pattern434 6 L;
      let patterns : Unit → SourcePattern
        (sourceNativeOriginalBigType434 6 L) 1 1 := fun _ => pat;
      ∃ (aux : SourceBigAux (SourceNativeMemoryBP434 6 L) 1 1 pat)
        (x : FullPhysicalState
          (SourceNativeMemorySP434 6 L hS) (fun _ p => p.val)
          (SourceNativeMemoryBP434 6 L) (fun _ p => p.val)
          1 (fun _ => 0))
        (b : FullPhysicalEdgeBranch
          (SourceNativeMemorySP434 6 L hS) (fun _ p => p.val)
          (SourceNativeMemoryBP434 6 L) (fun _ p => p.val)
          1 (fun _ => 0) x),
        (⟨(),(aux,b)⟩ : SourcePhysicalChoice
          (SourceNativeMemorySP434 6 L hS) (fun _ p => p.val)
          (SourceNativeMemoryBP434 6 L) (fun _ p => p.val)
          1 0 1 (fun _ => 0) patterns x) ∈
          legalSourcePhysicalChoices
            (SourceNativeMemorySP434 6 L hS) (fun _ p => p.val)
            (SourceNativeMemoryBP434 6 L) (fun _ p => p.val)
            1 0 1 (fun _ => 0) patterns x 1 2 ∧
        groupEdgeAllowedPerm
          (SourceNativeMemorySP434 6 L hS) (fun _ p => p.val) 1
          (sourceSmallShared 1 0)
          (sourcePhysicalStep
            (SourceNativeMemorySP434 6 L hS) (fun _ p => p.val)
            (SourceNativeMemoryBP434 6 L) (fun _ p => p.val)
            1 0 1 (fun _ => 0) pat aux x 1 2)
          (fun _ => Equiv.refl _) (fun _ => Equiv.refl _)
          x.1 b.smallTarget := by
  classical
  filter_upwards [
    source_native_r6_cofinal_L_tendsto_atTop434.eventually
      (eventually_native_original_ALL_P_spare_auxiliary434 6 (by norm_num)),
    eventually_ge_atTop (1:ℕ)]
    with N hSpare hN
  refine ⟨hN, ?_⟩
  let L := sourceNativeR6CofinalL434 N
  let hS := source_native_r6_cofinal_SMALL_nonempty434 N
  let SG := SourceNativeMemorySG434 6 L hS
  let BG := sourceNativeOriginalBigType434 6 L
  let SP := SourceNativeMemorySP434 6 L hS
  let BP := SourceNativeMemoryBP434 6 L
  obtain ⟨p,q,hp,hq,hNe,hAvoid⟩ := hSpare.2
  let smallAll : SG → sourceOriginalPAllGroupType 6 L := fun g =>
    match g with
    | none => sourceNativeOriginalSGroup434 6 L hS
    | some i => sourceNativeOriginalTsGroup434 6 L hS i
  let bigAll : BG → sourceOriginalPAllGroupType 6 L :=
    sourceNativeOriginalBigToAll434 6 L
  have hPSmall : ∀ g : SG, p (smallAll g) ∈
      SourceNativeMemorySmallSet434 6 L hS g := by
    intro g
    cases g with
    | none => exact hp (sourceNativeOriginalSGroup434 6 L hS)
    | some i => exact hp (sourceNativeOriginalTsGroup434 6 L hS i)
  have hPBig : ∀ g : BG, p (bigAll g) ∈
      sourceNativeOriginalTb434 6 L g := fun g => hp (bigAll g)
  have hQBig : ∀ g : BG, q (bigAll g) ∈
      sourceNativeOriginalTb434 6 L g := fun g => hq (bigAll g)
  let ps : (g : SG) → SP g := fun g =>
    ⟨p (smallAll g),hPSmall g⟩
  let pb : (g : BG) → BP g := fun g =>
    ⟨p (bigAll g),hPBig g⟩
  let qb : (g : BG) → BP g := fun g =>
    ⟨q (bigAll g),hQBig g⟩
  have hDifferent : ∀ g : BG, qb g ≠ pb g := by
    intro g h
    have heq : q (bigAll g)=p (bigAll g) :=
      congrArg Subtype.val h
    exact hNe (bigAll g) heq
  have hLegal := source_original_FULL_PHYSICAL_J1_m1_vacuum_legal434
    SP (fun _ pp => pp.val)
    BP (fun _ pp => pp.val)
    ps pb qb hDifferent (2:ℤ) (by norm_num)
  obtain ⟨x,b,hLegal,hSmallSupported⟩ := hLegal
  let pat := source_native_actual_J1_m1_pattern434 6 L
  let patterns : Unit → SourcePattern BG 1 1 := fun _ => pat
  let aux : SourceBigAux BP 1 1 pat := fun g _ => qb g
  refine ⟨aux,x,b,?_,?_⟩
  change
    (⟨(),(aux,b)⟩ : SourcePhysicalChoice SP (fun _ pp => pp.val)
      BP (fun _ pp => pp.val)
      1 0 1 (fun _ => 0) patterns x) ∈
    (Finset.univ.filter
      (SourcePhysicalLegal SP (fun _ pp => pp.val)
        BP (fun _ pp => pp.val)
        1 0 1 (fun _ => 0) patterns x 1 (2:ℤ)))
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  simpa only [aux,patterns,pat,SP,BP,SG,BG,ps,pb,qb,
    source_native_actual_J1_m1_aux434,
    source_native_actual_J1_m1_pattern434] using hLegal
  · simpa only [aux,patterns,pat,SP,BP,SG,BG,ps,pb,qb,
      source_native_actual_J1_m1_aux434,
      source_native_actual_J1_m1_pattern434] using hSmallSupported
end Green64Analytic.SourceBlockSieve

end

end

/-! ## SourceNativeR6NonvacuousBIGFreeRAW -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64ComparisonPartial Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- On the genuinely cofinal ORIGINAL source r=6 dyadic geometric
scales L_N=((3/2)2^N)^10, N>=1, the canonical FULL-G
four-sign J=1 common-RAW harmonic scalar is not only positive
but admits a fully CONSTRUCTED nonempty original BIG-free sector:
- every SMALL S/Ts and BIG Tb group supplies a real endpoint prime;
- all BIG free sets are genuine singletons {0}, with m=1 and J=1;
- every independently sampled BIG auxiliary q_g is a real prime
  from its unmodified original BIG band;
- every q_g avoids ALL endpoint prime factors, not only its own group;
- the endpoint product is <=exp(2L_N), with nonempty free marks;
- the projected RAW coefficient differs from one by L_N^-1,
  hence its real part is >=1/2.

No dummy BIG auxiliary, conditional law, fictional SourceComparisonData
or false Fock/OLD legal transfer is introduced. This proves a
NONEMPTY SOURCE ARITHMETIC J-HISTORY sector, not the original
complete SOURCE03 Comparison-integral or prime positivity. -/
theorem eventually_native_r6_NONVACUOUS_BIG_FREE_J1_RAW_positive434 :
    ∀ᶠ N : ℕ in atTop,
      1 ≤ N ∧
      ∃ (w : ℕ)
        (A : SourceNativeOriginalAllP434 6
          (sourceNativeR6CofinalL434 N) → Finset ℕ)
        (pat : SourcePattern
          (sourceNativeOriginalBigType434 6
            (sourceNativeR6CofinalL434 N)) 1 1)
        (aux : SourceBigAux
          (SourceNativeMemoryBP434 6
            (sourceNativeR6CofinalL434 N)) 1 1 pat),
        0 < w ∧
        (w:ℝ) ≤ Real.exp (2*sourceNativeR6CofinalL434 N) ∧
        (∀ g, 0 < (A g).card) ∧
        (∀ g, A g ⊆ w.primeFactors) ∧
        (∀ g : sourceNativeOriginalBigType434 6
          (sourceNativeR6CofinalL434 N), (pat.free g).card=1) ∧
        (∀ (g : sourceNativeOriginalBigType434 6
           (sourceNativeR6CofinalL434 N))
           (j : ↥(pat.free g)), (aux g j).val ∉ w.primeFactors) ∧
        ‖sourceNativeOriginalALLPJTrueProjectedRAW434 6
          (sourceNativeR6CofinalL434 N) 1
          (sourceNativeOriginalG434 6
            (sourceNativeR6CofinalL434 N)) A A-1‖ ≤
          (sourceNativeR6CofinalL434 N)^(-1:ℝ) ∧
        (1/2:ℝ) ≤
          (sourceNativeOriginalALLPJTrueProjectedRAW434 6
            (sourceNativeR6CofinalL434 N) 1
            (sourceNativeOriginalG434 6
              (sourceNativeR6CofinalL434 N)) A A).re := by
  classical
  let Lseq := sourceNativeR6CofinalL434
  have hT := source_native_r6_cofinal_L_tendsto_atTop434
  filter_upwards [
    hT.eventually (eventually_native_original_ALL_P_TRUE_BIG_FREE_nonvacuous434
      6 (by norm_num)),
    eventually_native_r6_COFINAL_ODD_J_TRUE_RAW_one434
      1 1 (by norm_num : Odd 1) 1,
    hT.eventually (eventually_ge_atTop (2:ℝ)),
    eventually_ge_atTop (1:ℕ)]
    with N hSource hRaw hL2 hN
  refine ⟨hN, ?_⟩
  let L := Lseq N
  obtain ⟨w,A,pat,aux,hw,hWcap,hApos,hAsub,hFree,hAux⟩ := hSource.2
  let Z : ℂ := sourceNativeOriginalALLPJTrueProjectedRAW434
    6 L 1 (sourceNativeOriginalG434 6 L) A A
  have hZ : ‖Z-1‖ ≤ L^(-1:ℝ) :=
    hRaw.2 1 pat aux (by norm_num) w w hw hw
      hWcap hWcap A A hApos hApos hAsub hAsub
  have hLp : 0 < L := by linarith
  have hInv : L^(-1:ℝ) ≤ (1/2:ℝ) := by
    rw [Real.rpow_neg_one,← one_div]
    exact (div_le_iff₀ hLp).mpr (by nlinarith [hL2])
  have hReal : (1/2:ℝ) ≤ Z.re := by
    have habs : |Z.re-1| ≤ ‖Z-1‖ := by
      simpa only [Complex.sub_re, Complex.one_re]
        using Complex.abs_re_le_norm (Z-1)
    have hlow := (abs_le.mp habs).1
    linarith [hZ,hInv,hlow]
  exact ⟨w,A,pat,aux,hw,hWcap,hApos,hAsub,hFree,hAux,hZ,hReal⟩
end Green64Analytic.SourceBlockSieve

end

end

/-! ## SourceNativeTrueBIGComparisonHPacket -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 7500000

/-- The REAL original independent BIG free source prime
at the one actual J=1,m=1 free slot of each original Tb band.
The dependent subtype is precisely the original BIG band,
not a replacement or conditional reweighted sample. -/
noncomputable def source_native_original_TRUE_BIG_free_prime434
    (r : ℕ) (L : ℝ)
    (aux : SourceBigAux (SourceNativeMemoryBP434 r L) 1 1
      (source_native_actual_J1_m1_pattern434 r L))
    (g : sourceNativeOriginalBigType434 r L) : ℕ :=
  (aux g ⟨(0:Fin 1), by
    simp [source_native_actual_J1_m1_pattern434]⟩).val

/-- The genuine original BIG free prime obeys BOTH exact
source tau=3/10 and 2/5 log-size exponents and is prime.
This is a source-domain theorem without an extra
prime-support assumption. -/
theorem source_native_original_TRUE_BIG_free_prime_bounds434
    (r : ℕ) (L : ℝ)
    (aux : SourceBigAux (SourceNativeMemoryBP434 r L) 1 1
      (source_native_actual_J1_m1_pattern434 r L))
    (g : sourceNativeOriginalBigType434 r L) :
    let q := source_native_original_TRUE_BIG_free_prime434 r L aux g
    q.Prime ∧
    Real.exp (L^(3/10:ℝ)) ≤ (q:ℝ) ∧
    (q:ℝ) ≤ Real.exp (L^(2/5:ℝ)) := by
  let q := source_native_original_TRUE_BIG_free_prime434 r L aux g
  have hmem : q ∈ sourceNativeOriginalTb434 r L g := by
    change (aux g ⟨(0:Fin 1), by
      simp [source_native_actual_J1_m1_pattern434]⟩).val ∈
      sourceNativeOriginalTb434 r L g
    exact (aux g _).property
  exact source_native_original_Tb_prime_range434 r L g q hmem

/-- The original nonempty BIG-free sector directly supplies
real source \`SourceComparisonData434\` fields
F1,F2,p1,p2,U1,U2,Hprime:
* each F_i is a NONEMPTY singleton;
* p_i is the actual source Tb prime from independent aux slots
  (not a fabricated free prime or the RAW-none Hprime=1);
* every p_i >= exp(L^3/10), and every p_i>=1;
* actual product cell bounds are literal equalities, not new
  shortened-cofactor bounds;
* U_i>0 and Hprime=U1*U2 exactly.

This proves only THESE named fields. The original comparison
record's other fields, endpoint K, QSkip arc and full D61
comparison-integral are still open. -/
theorem source_native_original_TRUE_BIG_F1_F2_Hprime_fields434
    (r : ℕ) (L : ℝ)
    (aux : SourceBigAux (SourceNativeMemoryBP434 r L) 1 1
      (source_native_actual_J1_m1_pattern434 r L))
    (g1 g2 : sourceNativeOriginalBigType434 r L) :
    let q1 := source_native_original_TRUE_BIG_free_prime434 r L aux g1
    let q2 := source_native_original_TRUE_BIG_free_prime434 r L aux g2
    let F1 : Finset ℕ := {0}
    let F2 : Finset ℕ := {0}
    let p1 : ℕ → ℕ := fun _ => q1
    let p2 : ℕ → ℕ := fun _ => q2
    let U1 : ℝ := (q1:ℝ)
    let U2 : ℝ := (q2:ℝ)
    let Hprime : ℝ := U1*U2
    F1.Nonempty ∧ F2.Nonempty ∧
    (∀ i∈F1, 1 ≤ p1 i) ∧
    (∀ i∈F2, 1 ≤ p2 i) ∧
    (∀ i∈F1, Real.exp (L^(3/10:ℝ)) ≤ (p1 i:ℝ)) ∧
    (∀ i∈F2, Real.exp (L^(3/10:ℝ)) ≤ (p2 i:ℝ)) ∧
    0<U1 ∧ 0<U2 ∧
    Real.log (((∏ i∈F1, p1 i:ℕ):ℝ)) ≤ Real.log U1+1 ∧
    Real.log (((∏ i∈F2, p2 i:ℕ):ℝ)) ≤ Real.log U2+1 ∧
    Hprime=U1*U2 ∧
    0<Hprime := by
  classical
  let q1 := source_native_original_TRUE_BIG_free_prime434 r L aux g1
  let q2 := source_native_original_TRUE_BIG_free_prime434 r L aux g2
  have hq1 := source_native_original_TRUE_BIG_free_prime_bounds434
    r L aux g1
  have hq2 := source_native_original_TRUE_BIG_free_prime_bounds434
    r L aux g2
  have hq1pos : 0 < q1 := hq1.1.pos
  have hq2pos : 0 < q2 := hq2.1.pos
  have hq1one : 1 ≤ q1 := hq1.1.one_le
  have hq2one : 1 ≤ q2 := hq2.1.one_le
  have hQ1 : (0:ℝ)<q1 := by exact_mod_cast hq1pos
  have hQ2 : (0:ℝ)<q2 := by exact_mod_cast hq2pos
  dsimp only
  refine ⟨by simp,by simp,?_,?_,?_,?_,hQ1,hQ2,?_,?_,rfl,?_⟩
  · intro i hi
    exact hq1one
  · intro i hi
    exact hq2one
  · intro i hi
    exact hq1.2.1
  · intro i hi
    exact hq2.2.1
  · simp only [Finset.prod_singleton]
    linarith
  · simp only [Finset.prod_singleton]
    linarith
  · positivity
end Green64Analytic.SourceBlockSieve

end

end

/-! ## SourceNativeActualBIGPhysicalHband -/

section

open Filter Real Asymptotics
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 8500000

/-- A real source BIG P-prime of size >=exp(L^(3/10))
dominates EVERY FIXED polylogarithmic endpoint arc factor
L^Carc. For sufficiently large L:
   2 L^Carc <= exp(L^(3/10)).
This is not a generic assumed hHband; it follows from the
genuine 3/10 original BIG prime exponent and log=o(L^3/10).
The source Carc is fixed BEFORE L, as in SourceComparisonFixed434. -/
theorem eventually_native_original_TRUE_BIG_prime_arc_lower434
    (Carc : ℝ) (hCarc : 0 ≤ Carc) :
    ∀ᶠ L : ℝ in atTop,
      Real.exp 1 ≤ L ∧
      2*L^Carc ≤ Real.exp (L^(3/10:ℝ)) := by
  let A : ℝ := Carc+2
  have hA : 0 < A := by dsimp [A]; linarith
  have hTiny := (isLittleO_log_rpow_atTop
    (by norm_num : (0:ℝ)<(3/10:ℝ))).bound
      (show (0:ℝ)<1/A by positivity)
  filter_upwards [hTiny, eventually_ge_atTop (Real.exp 1)]
    with L hbd hL
  refine ⟨hL, ?_⟩
  have hLp : 0 < L := (Real.exp_pos 1).trans_le hL
  have hL1 : 1 ≤ L :=
    (Real.one_le_exp (by norm_num : (0:ℝ)≤1)).trans hL
  have hLog : 0 ≤ Real.log L := Real.log_nonneg hL1
  have hPow : 0 ≤ L^(3/10:ℝ) :=
    Real.rpow_nonneg hLp.le _
  have hSmall : Real.log L ≤ (1/A)*L^(3/10:ℝ) := by
    simpa only [Real.norm_eq_abs,abs_of_nonneg hLog,
      abs_of_nonneg hPow] using hbd
  have hBound : A*Real.log L ≤ L^(3/10:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hSmall hA.le
    have hInv : A*(1/A)=1 := by field_simp [ne_of_gt hA]
    nlinarith [hh]
  have hL2 : (2:ℝ) ≤ L := by
    have h2 : (2:ℝ) ≤ Real.exp 1 := by
      nlinarith [Real.add_one_le_exp (1:ℝ)]
    exact h2.trans hL
  have hLog2 : Real.log (2:ℝ) ≤ Real.log L :=
    Real.log_le_log (by norm_num) hL2
  have hArg : Real.log (2:ℝ)+Carc*Real.log L ≤
      L^(3/10:ℝ) := by
    dsimp [A] at hBound
    nlinarith
  calc
    2*L^Carc = Real.exp (Real.log 2+Carc*Real.log L) := by
      rw [Real.rpow_def_of_pos hLp, Real.exp_add,
        Real.exp_log (by norm_num : (0:ℝ)<2)]
      ring
    _ ≤ Real.exp (L^(3/10:ℝ)) :=
      Real.exp_le_exp.mpr hArg

/-- The genuinely nonempty ORIGINAL physical BIG free source choice
supplies a comparator Hprime=U1*U2 with NO RAW-none dummy H'=1:
for ANY actual two BIG free prime slots, the exact unchanged
SOURCE03 arc condition \`hHband: 2<=Hprime/L^Carc\` holds
uniformly for sufficiently large L. The genuine Hprime
uses two actual primes from source BIG bands, each
>=exp(L^(3/10)), so this result is unconditional apart from the
existence of the original dependent BIG free sector already
constructed and checked elsewhere.

Remaining Y/Z/Ncap/Q/alpha/Fourier SourceComparisonData434 fields
are not claimed constructed here. -/
theorem eventually_native_original_TRUE_BIG_Hprime_hHband434
    (r : ℕ) (Carc : ℝ) (hCarc : 0 ≤ Carc) :
    ∀ᶠ L : ℝ in atTop,
      1 ≤ L ∧
      ∀ (aux : SourceBigAux (SourceNativeMemoryBP434 r L) 1 1
          (source_native_actual_J1_m1_pattern434 r L))
        (g1 g2 : sourceNativeOriginalBigType434 r L),
      let q1 := source_native_original_TRUE_BIG_free_prime434 r L aux g1
      let q2 := source_native_original_TRUE_BIG_free_prime434 r L aux g2
      2 ≤ ((q1:ℝ)*(q2:ℝ))/L^Carc := by
  filter_upwards [
    eventually_native_original_TRUE_BIG_prime_arc_lower434 Carc hCarc]
    with L h
  refine ⟨(Real.one_le_exp (by norm_num : (0:ℝ)≤1)).trans h.1, ?_⟩
  intro aux g1 g2
  let q1 := source_native_original_TRUE_BIG_free_prime434 r L aux g1
  let q2 := source_native_original_TRUE_BIG_free_prime434 r L aux g2
  have hq1 := source_native_original_TRUE_BIG_free_prime_bounds434
    r L aux g1
  have hq2 := source_native_original_TRUE_BIG_free_prime_bounds434
    r L aux g2
  have hp2 : (1:ℝ) ≤ (q2:ℝ) := by
    exact_mod_cast hq2.1.one_le
  have hp1 : (0:ℝ) ≤ (q1:ℝ) :=
    (Nat.cast_nonneg _)
  have hLo : Real.exp (L^(3/10:ℝ)) ≤ (q1:ℝ)*(q2:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hp2 hp1
    nlinarith [hq1.2.1,hh]
  have hL1 : 1 ≤ L :=
    (Real.one_le_exp (by norm_num : (0:ℝ)≤1)).trans h.1
  have hPow : 0 < L^Carc := Real.rpow_pos_of_pos
    (by linarith : (0:ℝ)<L) _
  apply (le_div_iff₀ hPow).mpr
  exact h.2.trans hLo
end Green64Analytic.SourceBlockSieve

end

end

/-! ## SourceNativeTruePhysicalPtwSigns -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- SOURCE03 actually permits Ptw⊆G, not only Ptw=G. For any
genuine Ptw and the ACTUAL sourceOrientedPhysicalD, the two
INDEPENDENT source/target parity choices transport with the
exact Ptw multiplicity parity of the physical Fock D:
   sign_b1(D*w) sign_b2(D*wp) =
   epsilon_Ptw(D)^(b1+b2) sign_b1(w) sign_b2(w).
No assumption that the Ptw phase is constant across Fock states
or that selected source primes are distinct. The original source
projector must retain this phase before the physical pattern sum.

For Ptw=G it reduces to the separately checked deterministic
(-1)^(J*(#S/Ts+#Tb)) phase; this theorem is stronger for the
literal optional Ptw subset used by original source comparisons. -/
theorem source_native_original_TRUE_PHYSICAL_D_Ptw_independent_signs434
    (r : ℕ) (L : ℝ)
    (hS : (sourceNativeOriginalSmallIndices434 r L).Nonempty)
    (J ell mFree : ℕ)
    (cap : sourceNativeOriginalBigType434 r L → ℕ)
    (pat : SourcePattern (sourceNativeOriginalBigType434 r L) J mFree)
    (aux : SourceBigAux (SourceNativeMemoryBP434 r L) J mFree pat)
    (x : FullPhysicalState
      (SourceNativeMemorySP434 r L hS) (fun _ p => p.val)
      (SourceNativeMemoryBP434 r L) (fun _ p => p.val)
      (J+ell) cap)
    (bs : BigGroupPerm (BG := sourceNativeOriginalBigType434 r L) (J+ell))
    (ss : GroupPermFamily
      (G := SourceNativeMemorySG434 r L hS) (J+ell))
    (Ptw : Finset ℕ) (w wp : ℕ)
    (hw : 0<w) (hwp : 0<wp) (b1 b2 : Bool) :
    let D := sourceOrientedPhysicalD
      (SourceNativeMemorySP434 r L hS) (fun _ p => p.val)
      (SourceNativeMemoryBP434 r L) (fun _ p => p.val)
      J ell mFree cap pat aux x bs ss
    let parityCount := ∑ p ∈ Ptw, D.factorization p
    sourceEndpointSign434 Ptw b1 (D*w) *
      sourceEndpointSign434 Ptw b2 (D*wp) =
      ((if b1 then (-1:ℂ)^parityCount else 1) *
       (if b2 then (-1:ℂ)^parityCount else 1)) *
        sourceEndpointSign434 Ptw b1 w *
        sourceEndpointSign434 Ptw b2 wp := by
  classical
  let D := sourceOrientedPhysicalD
    (SourceNativeMemorySP434 r L hS) (fun _ p => p.val)
    (SourceNativeMemoryBP434 r L) (fun _ p => p.val)
    J ell mFree cap pat aux x bs ss
  let parityCount := ∑ p ∈ Ptw, D.factorization p
  have hD := source_native_original_FULL_PHYSICAL_D_pos434
    r L hS J ell mFree cap pat aux x bs ss
  have hParity : literalSourceParity Ptw D =
      (-1:ℂ)^parityCount := rfl
  exact source_shared_dilation_independent_signs434
    Ptw D w wp parityCount b1 b2
    (Nat.ne_of_gt hD) (Nat.ne_of_gt hw) (Nat.ne_of_gt hwp)
    hParity

/-- The literal Ptw SUBSET physical D parity transport factor has
modulus exactly one for all four independent endpoint sign pairs.
It must not be replaced by 1 if source/target sign choices differ. -/
theorem source_native_original_TRUE_PHYSICAL_D_Ptw_phase_norm434
    (Ptw : Finset ℕ) (D : ℕ) (b1 b2 : Bool) :
    ‖(if b1 then literalSourceParity Ptw D else 1) *
      (if b2 then literalSourceParity Ptw D else 1)‖ = 1 := by
  simpa only [literalSourceParity] using
    source_shared_pattern_sign_norm434
      (∑ p ∈ Ptw, D.factorization p) b1 b2

/-- Equal parity choices at BOTH original endpoints cancel the
genuine Fock D phase exactly, for every physical Ptw⊆G and
all repeated source prime valuations. -/
theorem source_native_original_TRUE_PHYSICAL_D_Ptw_same_sign_cancel434
    (r : ℕ) (L : ℝ)
    (hS : (sourceNativeOriginalSmallIndices434 r L).Nonempty)
    (J ell mFree : ℕ)
    (cap : sourceNativeOriginalBigType434 r L → ℕ)
    (pat : SourcePattern (sourceNativeOriginalBigType434 r L) J mFree)
    (aux : SourceBigAux (SourceNativeMemoryBP434 r L) J mFree pat)
    (x : FullPhysicalState
      (SourceNativeMemorySP434 r L hS) (fun _ p => p.val)
      (SourceNativeMemoryBP434 r L) (fun _ p => p.val)
      (J+ell) cap)
    (bs : BigGroupPerm (BG := sourceNativeOriginalBigType434 r L) (J+ell))
    (ss : GroupPermFamily
      (G := SourceNativeMemorySG434 r L hS) (J+ell))
    (Ptw : Finset ℕ) (w wp : ℕ)
    (hw : 0<w) (hwp : 0<wp) (choice : Bool) :
    let D := sourceOrientedPhysicalD
      (SourceNativeMemorySP434 r L hS) (fun _ p => p.val)
      (SourceNativeMemoryBP434 r L) (fun _ p => p.val)
      J ell mFree cap pat aux x bs ss
    sourceEndpointSign434 Ptw choice (D*w) *
      sourceEndpointSign434 Ptw choice (D*wp) =
    sourceEndpointSign434 Ptw choice w *
      sourceEndpointSign434 Ptw choice wp := by
  let D := sourceOrientedPhysicalD
    (SourceNativeMemorySP434 r L hS) (fun _ p => p.val)
    (SourceNativeMemoryBP434 r L) (fun _ p => p.val)
    J ell mFree cap pat aux x bs ss
  have hD := source_native_original_FULL_PHYSICAL_D_pos434
    r L hS J ell mFree cap pat aux x bs ss
  exact source_original_true_shared_common_parity434 Ptw D w wp
    (Nat.ne_of_gt hD) (Nat.ne_of_gt hw) (Nat.ne_of_gt hwp)
    choice
end Green64Analytic.SourceBlockSieve

end

end

/-! ## SourceNativeOriginalPPart -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 8500000

/-- Original endpoint's WHOLE P-part, with exact natural prime
factorization exponents (including multiplicity). The source
ordinary cofactor is the actual sourceOutsidePart P n.
The P-part and ordinary part multiply to n, with no artificial
squarefree assumption. -/
noncomputable def sourceOriginalNativePPart434 (P : Finset ℕ)
    (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors with p ∈ P, p^(n.factorization p)

/-- Every original positive source endpoint is precisely its full
P-valuation part times its exact original ordinary (P-free) part.
The divisor normalizations, repeated P prime powers and inclusive
source prime bands are unchanged. -/
theorem source_original_endpoint_P_part_outside_factorization434
    (P : Finset ℕ) (n : ℕ) (hn : n≠0) :
    sourceOriginalNativePPart434 P n *
      sourceOutsidePart P n = n := by
  classical
  have hTotal :
      (∏ p ∈ n.primeFactors, p^(n.factorization p)) = n := by
    have hh := Nat.prod_factorization_pow_eq_self hn
    change (∏ p ∈ n.factorization.support, p ^ n.factorization p) = n at hh
    simpa only [Nat.support_factorization] using hh
  have hSplit := Finset.prod_filter_mul_prod_filter_not
    n.primeFactors (fun p : ℕ => p ∈ P)
    (fun p : ℕ => p^(n.factorization p))
  exact hSplit.trans hTotal

/-- Prime factors of the actual P-part of an original integer
belong to the SAME source P-group union, with multiplicities
unrestricted. This supplies the previously explicit d1/d2
prime-support gates of the native D61 physical fibre theorem. -/
theorem source_original_P_part_prime_support434
    (P : Finset ℕ) (n p : ℕ)
    (hp : p.Prime)
    (hdiv : p ∣ sourceOriginalNativePPart434 P n) :
    p ∈ P := by
  classical
  have hprod {I : Type} [DecidableEq I] (S : Finset I)
      (f : I → ℕ) (q : ℕ) (hq : q.Prime)
      (hd : q ∣ ∏ i ∈ S, f i) :
      ∃ i ∈ S, q ∣ f i := by
    induction S using Finset.induction_on with
    | empty =>
        simp only [Finset.prod_empty] at hd
        exact (hq.not_dvd_one hd).elim
    | @insert i S hi ih =>
        rw [Finset.prod_insert hi] at hd
        rcases (hq.dvd_mul.mp hd) with h | h
        · exact ⟨i, Finset.mem_insert_self _ _, h⟩
        · obtain ⟨j,hj,hdj⟩ := ih h
          exact ⟨j,Finset.mem_insert_of_mem hj,hdj⟩
  unfold sourceOriginalNativePPart434 at hdiv
  obtain ⟨q,hq,hpq⟩ :=
    hprod (n.primeFactors.filter (fun q => q ∈ P))
      (fun q => q^(n.factorization q)) p hp hdiv
  have hqP : q ∈ P := (Finset.mem_filter.mp hq).2
  have hqPrime : q.Prime :=
    (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hq).1).1
  have hpq : p∣q := hp.dvd_of_dvd_pow hpq
  have he : p=q := (Nat.prime_dvd_prime_iff_eq hp hqPrime).mp hpq
  exact he.symm ▸ hqP

/-- This canonical LIST of all physical source P-part prime factors
includes multiplicities and reconstructs the actual P-part,
not a set of distinct labels or an arithmetic surrogate. -/
theorem source_original_P_part_prime_factor_list434
    (P : Finset ℕ) (n : ℕ) (hn : 0<n) :
    let d := sourceOriginalNativePPart434 P n
    d.primeFactorsList.prod = d ∧
      (∀ p ∈ d.primeFactorsList, p ∈ P) := by
  classical
  let d := sourceOriginalNativePPart434 P n
  have hdpos : 0<d := by
    dsimp [d,sourceOriginalNativePPart434]
    apply Finset.prod_pos
    intro p hp
    have hPrime : p.Prime :=
      (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hp).1).1
    exact pow_pos hPrime.pos _
  have hdne : d≠0 := Nat.ne_of_gt hdpos
  refine ⟨Nat.prod_primeFactorsList hdne, ?_⟩
  intro p hp
  have hprime := (Nat.mem_primeFactorsList hdne).mp hp
  exact source_original_P_part_prime_support434
    P n p hprime.1 hprime.2
end Green64Analytic.SourceBlockSieve

end

end

/-! ## SourceNativePhysicalOutsideCoprime -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 6500000

/-- The ORIGINAL SOURCE03 ordinary cofactor \`sourceOutsidePart P n\`
is coprime to every integer D all of whose prime factors lie in the
full source S/Ts/Tb P-group union. Multiplicities in n and D are
unrestricted. The literal original \`sourceOutsidePart\` factorization
is used, not a squarefree cofactor replacement. -/
theorem source_original_outside_part_coprime_P_divisor434
    (P : Finset ℕ) (n D : ℕ)
    (hD : ∀ p, p.Prime → p ∣ D → p ∈ P) :
    D.Coprime (sourceOutsidePart P n) := by
  classical
  unfold sourceOutsidePart
  apply Nat.Coprime.prod_right
  intro p hp
  obtain ⟨hpFac, hpNot⟩ := Finset.mem_filter.mp hp
  have hpprime : p.Prime := (Nat.mem_primeFactors.mp hpFac).1
  have hno : ¬p ∣ D := fun h => hpNot (hD p hpprime h)
  have hcop : D.Coprime p :=
    (hpprime.coprime_iff_not_dvd.mpr hno).symm
  exact hcop.pow_right _

/-- ACTUAL physical D from the ORIGINAL Fock state (SMALL S/Ts,
BIG shared, independent BIG free aux and all original permutations)
has no common prime factor with the ordinary outside-P cofactor
of ANY source endpoint n. No D|n assumption is needed. -/
theorem source_native_original_PHYSICAL_D_coprime_outside434
    (r : ℕ) (L : ℝ)
    (hS : (sourceNativeOriginalSmallIndices434 r L).Nonempty)
    (J ell mFree : ℕ)
    (cap : sourceNativeOriginalBigType434 r L → ℕ)
    (pat : SourcePattern (sourceNativeOriginalBigType434 r L) J mFree)
    (aux : SourceBigAux (SourceNativeMemoryBP434 r L) J mFree pat)
    (x : FullPhysicalState
      (SourceNativeMemorySP434 r L hS) (fun _ p => p.val)
      (SourceNativeMemoryBP434 r L) (fun _ p => p.val)
      (J+ell) cap)
    (bs : BigGroupPerm (BG := sourceNativeOriginalBigType434 r L) (J+ell))
    (ss : GroupPermFamily
      (G := SourceNativeMemorySG434 r L hS) (J+ell))
    (n : ℕ) :
    let P := sourceNativeOriginalG434 r L
    let D := sourceOrientedPhysicalD
      (SourceNativeMemorySP434 r L hS) (fun _ p => p.val)
      (SourceNativeMemoryBP434 r L) (fun _ p => p.val)
      J ell mFree cap pat aux x bs ss
    D.Coprime (sourceOutsidePart P n) := by
  classical
  let P := sourceNativeOriginalG434 r L
  let D := sourceOrientedPhysicalD
    (SourceNativeMemorySP434 r L hS) (fun _ p => p.val)
    (SourceNativeMemoryBP434 r L) (fun _ p => p.val)
    J ell mFree cap pat aux x bs ss
  exact source_original_outside_part_coprime_P_divisor434
    P n D (fun p hp hdiv =>
      source_native_original_FULL_PHYSICAL_D_prime_support434
        r L hS J ell mFree cap pat aux x bs ss p hp hdiv)

/-- The original physical source D is in fact a divisor of the
entire P-VALUATION part of an endpoint n whenever the unchanged
source physical support asserts D | n. This removes a previously
independent "source D lives in the P-part" assumption:
D | full endpoint and prime support D⊆P imply
 D | sourceOriginalNativePPart434 P n.
No squarefree assumption and no lost repeated P prime valuations. -/
theorem source_native_original_PHYSICAL_D_dvd_P_part434
    (r : ℕ) (L : ℝ)
    (hS : (sourceNativeOriginalSmallIndices434 r L).Nonempty)
    (J ell mFree : ℕ)
    (cap : sourceNativeOriginalBigType434 r L → ℕ)
    (pat : SourcePattern (sourceNativeOriginalBigType434 r L) J mFree)
    (aux : SourceBigAux (SourceNativeMemoryBP434 r L) J mFree pat)
    (x : FullPhysicalState
      (SourceNativeMemorySP434 r L hS) (fun _ p => p.val)
      (SourceNativeMemoryBP434 r L) (fun _ p => p.val)
      (J+ell) cap)
    (bs : BigGroupPerm (BG := sourceNativeOriginalBigType434 r L) (J+ell))
    (ss : GroupPermFamily
      (G := SourceNativeMemorySG434 r L hS) (J+ell))
    (n : ℕ) (hn : 0<n) :
    let P := sourceNativeOriginalG434 r L
    let D := sourceOrientedPhysicalD
      (SourceNativeMemorySP434 r L hS) (fun _ p => p.val)
      (SourceNativeMemoryBP434 r L) (fun _ p => p.val)
      J ell mFree cap pat aux x bs ss
    D ∣ n → D ∣ sourceOriginalNativePPart434 P n := by
  classical
  let P := sourceNativeOriginalG434 r L
  let D := sourceOrientedPhysicalD
    (SourceNativeMemorySP434 r L hS) (fun _ p => p.val)
    (SourceNativeMemoryBP434 r L) (fun _ p => p.val)
    J ell mFree cap pat aux x bs ss
  change D ∣ n → D ∣ sourceOriginalNativePPart434 P n
  intro hD
  have hFactor := source_original_endpoint_P_part_outside_factorization434
    P n (Nat.ne_of_gt hn)
  have hCop : D.Coprime (sourceOutsidePart P n) :=
    source_native_original_PHYSICAL_D_coprime_outside434
      r L hS J ell mFree cap pat aux x bs ss n
  rw [←hFactor] at hD
  exact hCop.dvd_of_dvd_mul_right hD
end Green64Analytic.SourceBlockSieve

end

end

/-! ## SourceNativePhysicalOutsideInvariant -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 8500000

/-- The LITERAL original source \`sourceOutsidePart P\` is EXACTLY
invariant under multiplying an ordinary positive endpoint by the
TRUE source oriented physical divisor D from the actual Fock state
(S, all Ts, all Tb, marked BIG shared and independent auxiliary).
Repeated selected prime values and full multiplicity are preserved:
the canonical primeFactorsList of D, NOT a deduplicated Finset of
prime values, is used to instantiate the verified labelled prime
product invariant. This is the missing literal source ordinary-core
transport for the entire physical D, without assuming a separate
external divisor prime list. -/
theorem source_native_original_PHYSICAL_D_outside_invariant434
    (r : ℕ) (L : ℝ)
    (hS : (sourceNativeOriginalSmallIndices434 r L).Nonempty)
    (J ell mFree : ℕ)
    (cap : sourceNativeOriginalBigType434 r L → ℕ)
    (pat : SourcePattern (sourceNativeOriginalBigType434 r L) J mFree)
    (aux : SourceBigAux (SourceNativeMemoryBP434 r L) J mFree pat)
    (x : FullPhysicalState
      (SourceNativeMemorySP434 r L hS) (fun _ p => p.val)
      (SourceNativeMemoryBP434 r L) (fun _ p => p.val)
      (J+ell) cap)
    (bs : BigGroupPerm (BG := sourceNativeOriginalBigType434 r L) (J+ell))
    (ss : GroupPermFamily
      (G := SourceNativeMemorySG434 r L hS) (J+ell))
    (n : ℕ) (hn : 0<n) :
    let P := sourceNativeOriginalG434 r L
    let D := sourceOrientedPhysicalD
      (SourceNativeMemorySP434 r L hS) (fun _ p => p.val)
      (SourceNativeMemoryBP434 r L) (fun _ p => p.val)
      J ell mFree cap pat aux x bs ss
    sourceOutsidePart P (D*n) = sourceOutsidePart P n := by
  classical
  let P := sourceNativeOriginalG434 r L
  let D := sourceOrientedPhysicalD
    (SourceNativeMemorySP434 r L hS) (fun _ p => p.val)
    (SourceNativeMemoryBP434 r L) (fun _ p => p.val)
    J ell mFree cap pat aux x bs ss
  let dlist : List ℕ := D.primeFactorsList
  have hFactors := source_native_original_FULL_PHYSICAL_D_prime_factor_list434
    r L hS J ell mFree cap pat aux x bs ss
  have hDpos := source_native_original_FULL_PHYSICAL_D_pos434
    r L hS J ell mFree cap pat aux x bs ss
  have hDne : D ≠ 0 := Nat.ne_of_gt hDpos
  have hPrime : ∀ i : Fin dlist.length,
      (dlist.get i).Prime := by
    intro i
    exact (Nat.mem_primeFactorsList hDne).mp
      (List.get_mem dlist i) |>.1
  have hMem : ∀ i : Fin dlist.length, dlist.get i ∈ P := by
    intro i
    exact hFactors.2 (dlist.get i) (List.get_mem dlist i)
  have hProd : (∏ i : Fin dlist.length, dlist.get i)=D := by
    calc
      _ = (List.ofFn dlist.get).prod := (List.prod_ofFn).symm
      _ = dlist.prod := by rw [List.ofFn_get]
      _ = D := hFactors.1
  have hInvariant := source_auxiliary_original_labelled_outside_invariant434
    (Finset.univ : Finset (Fin dlist.length))
    dlist.get P n
    (by intro i hi; exact hPrime i)
    (by intro i hi; exact hMem i)
    hn
  change sourceOutsidePart P (D*n)=sourceOutsidePart P n
  simpa only [hProd] using hInvariant

/-- The genuine original source ordinary QSkip/character core F(n)
is invariant under multiplication by the EXACT full physical Fock D,
with all signed source Fourier variables, original primeSlot, alpha,
full literal c(v), and q-character preserved.

This identity is at the original sourceCore/sourceOutsidePart level.
The entire four-channel RAW physical operator (including OLD,
Fock/history and terminal vacuum) is not claimed equal to the
comparison integral by this arithmetic lemma alone. -/
theorem source_native_original_PHYSICAL_D_sourceCore_invariant434
    (r : ℕ) (L : ℝ)
    (hS : (sourceNativeOriginalSmallIndices434 r L).Nonempty)
    (J ell mFree : ℕ)
    (cap : sourceNativeOriginalBigType434 r L → ℕ)
    (pat : SourcePattern (sourceNativeOriginalBigType434 r L) J mFree)
    (aux : SourceBigAux (SourceNativeMemoryBP434 r L) J mFree pat)
    (x : FullPhysicalState
      (SourceNativeMemorySP434 r L hS) (fun _ p => p.val)
      (SourceNativeMemoryBP434 r L) (fun _ p => p.val)
      (J+ell) cap)
    (bs : BigGroupPerm (BG := sourceNativeOriginalBigType434 r L) (J+ell))
    (ss : GroupPermFamily
      (G := SourceNativeMemorySG434 r L hS) (J+ell))
    (n : ℕ) (hn : 0<n)
    (primeSlot : Finset ℕ)
    (alpha c : ℕ → ℂ)
    (q : ℕ) (chi : DirichletCharacter ℂ q)
    (s0 s1 : ℝ) :
    let P := sourceNativeOriginalG434 r L
    let D := sourceOrientedPhysicalD
      (SourceNativeMemorySP434 r L hS) (fun _ p => p.val)
      (SourceNativeMemoryBP434 r L) (fun _ p => p.val)
      J ell mFree cap pat aux x bs ss
    sourceCore (sourceOutsidePart P (D*n))
      primeSlot alpha c q chi s0 s1 =
    sourceCore (sourceOutsidePart P n)
      primeSlot alpha c q chi s0 s1 := by
  dsimp only
  rw [source_native_original_PHYSICAL_D_outside_invariant434
    r L hS J ell mFree cap pat aux x bs ss n hn]
end Green64Analytic.SourceBlockSieve

end

end

/-! ## SourceNativeTruePhysicalTwoEndCore -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 8500000

/-- Two ORIGINAL SOURCE03 ordinary QSkip-character sourceCore
functions, with independent full Fourier/character coefficients
and independent Ptw endpoint parity choices, transported through
the SAME true physical Fock D selected from original SMALL S/Ts
and BIG marked/free auxiliaries.

The true physical parity phase survives iff the two endpoint sign
choices differ; it is retained as a complex unit factor, NOT
illegally cancelled before the full four-sign pattern sum. The
ordinary sourceCore/outsidePart components on BOTH ends are EXACTLY
invariant under D, including repeated labels.

This is a finite SCALAR source kernel identity and does not assert
an equality of the full B8 memory/OLD/terminal-vacuum operators or
the actual Fourier-integrated source comparison functional. -/
theorem source_native_original_TRUE_PHYSICAL_D_two_end_signedCore434
    (r : ℕ) (L : ℝ)
    (hS : (sourceNativeOriginalSmallIndices434 r L).Nonempty)
    (J ell mFree : ℕ)
    (cap : sourceNativeOriginalBigType434 r L → ℕ)
    (pat : SourcePattern (sourceNativeOriginalBigType434 r L) J mFree)
    (aux : SourceBigAux (SourceNativeMemoryBP434 r L) J mFree pat)
    (x : FullPhysicalState
      (SourceNativeMemorySP434 r L hS) (fun _ p => p.val)
      (SourceNativeMemoryBP434 r L) (fun _ p => p.val)
      (J+ell) cap)
    (bs : BigGroupPerm (BG := sourceNativeOriginalBigType434 r L) (J+ell))
    (ss : GroupPermFamily
      (G := SourceNativeMemorySG434 r L hS) (J+ell))
    (Ptw : Finset ℕ) (w wp : ℕ)
    (hw : 0<w) (hwp : 0<wp) (b1 b2 : Bool)
    (primeSlot1 primeSlot2 : Finset ℕ)
    (alpha1 c1 alpha2 c2 : ℕ → ℂ)
    (q1 q2 : ℕ) (chi1 : DirichletCharacter ℂ q1)
    (chi2 : DirichletCharacter ℂ q2)
    (s01 s11 s02 s12 : ℝ) :
    let P := sourceNativeOriginalG434 r L
    let D := sourceOrientedPhysicalD
      (SourceNativeMemorySP434 r L hS) (fun _ p => p.val)
      (SourceNativeMemoryBP434 r L) (fun _ p => p.val)
      J ell mFree cap pat aux x bs ss
    let pcount := ∑ p ∈ Ptw, D.factorization p
    (sourceCore (sourceOutsidePart P (D*w))
        primeSlot1 alpha1 c1 q1 chi1 s01 s11 *
      sourceEndpointSign434 Ptw b1 (D*w)) *
    (sourceCore (sourceOutsidePart P (D*wp))
        primeSlot2 alpha2 c2 q2 chi2 s02 s12 *
      sourceEndpointSign434 Ptw b2 (D*wp)) =
    ((if b1 then (-1:ℂ)^pcount else 1) *
      (if b2 then (-1:ℂ)^pcount else 1)) *
    ((sourceCore (sourceOutsidePart P w)
        primeSlot1 alpha1 c1 q1 chi1 s01 s11 *
      sourceEndpointSign434 Ptw b1 w) *
     (sourceCore (sourceOutsidePart P wp)
        primeSlot2 alpha2 c2 q2 chi2 s02 s12 *
      sourceEndpointSign434 Ptw b2 wp)) := by
  classical
  let P := sourceNativeOriginalG434 r L
  let D := sourceOrientedPhysicalD
    (SourceNativeMemorySP434 r L hS) (fun _ p => p.val)
    (SourceNativeMemoryBP434 r L) (fun _ p => p.val)
    J ell mFree cap pat aux x bs ss
  let pcount := ∑ p ∈ Ptw, D.factorization p
  let F : ℂ := sourceCore (sourceOutsidePart P w)
    primeSlot1 alpha1 c1 q1 chi1 s01 s11
  let H : ℂ := sourceCore (sourceOutsidePart P wp)
    primeSlot2 alpha2 c2 q2 chi2 s02 s12
  let phase : ℂ := ((if b1 then (-1:ℂ)^pcount else 1) *
    (if b2 then (-1:ℂ)^pcount else 1))
  have hCore1 := source_native_original_PHYSICAL_D_sourceCore_invariant434
    r L hS J ell mFree cap pat aux x bs ss w hw
    primeSlot1 alpha1 c1 q1 chi1 s01 s11
  have hCore2 := source_native_original_PHYSICAL_D_sourceCore_invariant434
    r L hS J ell mFree cap pat aux x bs ss wp hwp
    primeSlot2 alpha2 c2 q2 chi2 s02 s12
  have hSign := source_native_original_TRUE_PHYSICAL_D_Ptw_independent_signs434
    r L hS J ell mFree cap pat aux x bs ss Ptw w wp hw hwp b1 b2
  change
    (sourceCore (sourceOutsidePart P (D*w))
       primeSlot1 alpha1 c1 q1 chi1 s01 s11 *
      sourceEndpointSign434 Ptw b1 (D*w)) *
    (sourceCore (sourceOutsidePart P (D*wp))
       primeSlot2 alpha2 c2 q2 chi2 s02 s12 *
      sourceEndpointSign434 Ptw b2 (D*wp)) =
    phase * ((F * sourceEndpointSign434 Ptw b1 w) *
      (H * sourceEndpointSign434 Ptw b2 wp))
  rw [hCore1,hCore2]
  calc
    (F * sourceEndpointSign434 Ptw b1 (D*w)) *
      (H * sourceEndpointSign434 Ptw b2 (D*wp)) =
      (F*H)*(sourceEndpointSign434 Ptw b1 (D*w) *
        sourceEndpointSign434 Ptw b2 (D*wp)) := by ring
    _ = (F*H)*(phase *
        (sourceEndpointSign434 Ptw b1 w *
        sourceEndpointSign434 Ptw b2 wp)) := by
        rw [hSign]
        dsimp only [phase,pcount]
        ring
    _ = phase*((F*sourceEndpointSign434 Ptw b1 w) *
        (H*sourceEndpointSign434 Ptw b2 wp)) := by ring
end Green64Analytic.SourceBlockSieve

end

end

/-! ## SourceOriginalTrueAllNuCardinalityAbsorb -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 11000000

/-- Exact polynomial absorption of the ACTUAL entire ν-pattern
cardinality squared in SOURCE03's proved full physical
signed C191/C6/discarded bound. No primitive character count
appears here, because each comparison residual is indexed by
ν ONCE. For the true BIG group count <= C0 log L:
  [2^(m(sA+sB))]^2 * 72000 L^-Bout <= 72000 L^-Bafter
provided Bout>=Bafter+2m*C0*log2. The exponent is fixed
independently of the later large slot-count J. -/
theorem source_original_true_all_nu_minor_cardinality_absorb434
    {G : Type} [DecidableEq G]
    (blockA blockB : Finset G) (m : ℕ)
    (L C0 Bout Bafter : ℝ) (hL : 1 ≤ L)
    (hGroups : (((blockA.card+blockB.card):ℕ):ℝ) ≤
      C0*Real.log L)
    (hExponent :
      Bafter+2*((m:ℝ)*C0*Real.log 2) ≤ Bout) :
    ((2^(m*(blockA.card+blockB.card)):ℝ)^2) *
        (72000*L^(-Bout)) ≤ 72000*L^(-Bafter) := by
  let E : ℝ := (m:ℝ)*C0*Real.log 2
  have hLpos : 0 < L := by linarith
  have hLnn : 0 ≤ L := hLpos.le
  have hFamily :
      (2:ℝ)^(m*(blockA.card+blockB.card)) ≤ L^E :=
    source_original_probe_two_power_log_bound434
      blockA blockB m L C0 hL hGroups
  have hFamNN :
      0 ≤ (2:ℝ)^(m*(blockA.card+blockB.card)) := by positivity
  have hFamilySq := pow_le_pow_left₀ hFamNN hFamily 2
  have hESq : (L^E)^2 = L^(2*E) := by
    calc
      (L^E)^2 = (L^E)^(2:ℝ) :=
        (Real.rpow_natCast (L^E) 2).symm
      _ = L^(E*2) := (Real.rpow_mul hLnn E (2:ℝ)).symm
      _ = L^(2*E) := by ring
  have hExp : 2*E-Bout ≤ -Bafter := by
    dsimp only [E] at hExponent ⊢
    linarith
  have hExpBound : L^(2*E-Bout) ≤ L^(-Bafter) :=
    Real.rpow_le_rpow_of_exponent_le hL hExp
  have hCostNonneg : 0 ≤ 72000*L^(-Bout) := by positivity
  calc
    _ ≤ (L^E)^2*(72000*L^(-Bout)) :=
      mul_le_mul_of_nonneg_right hFamilySq hCostNonneg
    _ = 72000*L^(2*E-Bout) := by
      rw [hESq,sub_eq_add_neg,Real.rpow_add hLpos]
      ring
    _ ≤ 72000*L^(-Bafter) :=
      mul_le_mul_of_nonneg_left hExpBound (by norm_num)
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalAllNuFullSignPolynomialLoss -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- SOURCE03 whole original nu-pattern family SQUARED
physical C191+C6+discarded budget after absorbing the
ACTUAL 2^(m*(sA+sB)) pattern multiplier. This includes
the C191 prefactor 3*K/Vmin+2, not just the C6 part.
With the original logarithmic group-count restriction
and explicit C191 coefficient growth, the FOUR sign
channels (each with the same L2 budget) satisfy
  familyCost^2 * perNuBudget <= 288006 L^-Dgoal.
The requisite exponents remain visible, not hidden in
big-O notation or a manufactured uniform test norm. -/
theorem source_original_true_all_nu_FULL_sign_loss_absorb434
    {G : Type} [DecidableEq G]
    (blockA blockB : Finset G) (m : ℕ)
    (L C0 Ck Bmaj Bout Dgoal K Vmin : ℝ)
    (hL : 1 ≤ L) (hC0 : 0 ≤ C0) (hCk : 0 ≤ Ck)
    (hGroups : (((blockA.card+blockB.card):ℕ):ℝ) ≤
      C0*Real.log L)
    (hK : 0 ≤ K) (hVmin : 0 < Vmin)
    (hC191 : 3*(K/Vmin)+2 ≤ L^Ck)
    (hMajorExp :
      Dgoal+2*((m:ℝ)*C0*Real.log 2)+2*Ck ≤ 2*Bmaj)
    (hMinorExp :
      Dgoal+2*((m:ℝ)*C0*Real.log 2) ≤ Bout) :
    let F : ℝ := 3*(K/Vmin)+2
    let eps : ℝ := F*L^(-Bmaj)
    let family : ℝ :=
      (2^(m*(blockA.card+blockB.card)):ℝ)
    family^2*
      (2*(2*(eps^2+72000*L^(-Bout))+L^(-(2*Bmaj)))) ≤
       288006*L^(-Dgoal) := by
  let E : ℝ := (m:ℝ)*C0*Real.log 2
  let F : ℝ := 3*(K/Vmin)+2
  let eps : ℝ := F*L^(-Bmaj)
  let family : ℝ :=
    (2^(m*(blockA.card+blockB.card)):ℝ)
  have hLpos : 0 < L := by linarith
  have hLnn : 0 ≤ L := hLpos.le
  have hFnn : 0 ≤ F := by dsimp only [F];positivity
  have hFamilyNN : 0 ≤ family := by dsimp only [family];positivity
  have hFamily : family ≤ L^E :=
    source_original_probe_two_power_log_bound434
      blockA blockB m L C0 hL hGroups
  have hFamilySq :
      family^2 ≤ L^(2*E) := by
    have hs := pow_le_pow_left₀ hFamilyNN hFamily 2
    calc
      _ ≤ (L^E)^2 := hs
      _ = L^(2*E) := by
        calc
          (L^E)^2 = (L^E)^(2:ℝ) :=
            (Real.rpow_natCast (L^E) 2).symm
          _ = L^(E*2) :=
            (Real.rpow_mul hLnn E (2:ℝ)).symm
          _ = L^(2*E) := by ring
  have hMajW : F^2 ≤ L^(2*Ck) := by
    have hh := pow_le_pow_left₀ hFnn
      (show F ≤ L^Ck by simpa only [F] using hC191) 2
    calc
      _ ≤ (L^Ck)^2 := hh
      _ = L^(2*Ck) := by
        calc
          (L^Ck)^2 = (L^Ck)^(2:ℝ) :=
            (Real.rpow_natCast (L^Ck) 2).symm
          _ = L^(Ck*2) :=
            (Real.rpow_mul hLnn Ck (2:ℝ)).symm
          _ = L^(2*Ck) := by ring
  have hNegPowSq :
      (L^(-Bmaj))^2 = L^(-(2*Bmaj)) := by
    calc
      (L^(-Bmaj))^2 = (L^(-Bmaj))^(2:ℝ) :=
        (Real.rpow_natCast (L^(-Bmaj)) 2).symm
      _ = L^((-Bmaj)*2) :=
        (Real.rpow_mul hLnn (-Bmaj) (2:ℝ)).symm
      _ = L^(-(2*Bmaj)) := by ring
  have hEpsBound : eps^2 ≤ L^(2*Ck-2*Bmaj) := by
    have hLnonneg : 0 ≤ L^(-(2*Bmaj)) :=
      Real.rpow_nonneg hLnn _
    calc
      _ = F^2*L^(-(2*Bmaj)) := by
        dsimp only [eps]
        rw [mul_pow,hNegPowSq]
      _ ≤ L^(2*Ck)*L^(-(2*Bmaj)) :=
        mul_le_mul_of_nonneg_right hMajW hLnonneg
      _ = L^(2*Ck-2*Bmaj) := by
        rw [sub_eq_add_neg,Real.rpow_add hLpos]
  have hExpMajor :
      2*E+(2*Ck-2*Bmaj) ≤ -Dgoal := by
    dsimp only [E] at hMajorExp ⊢
    linarith [hMajorExp]
  have hExpMinor : 2*E-Bout ≤ -Dgoal := by
    dsimp only [E] at hMinorExp ⊢
    linarith [hMinorExp]
  have hExpBad : 2*E-2*Bmaj ≤ -Dgoal := by
    linarith [hExpMajor,hCk]
  have hTermMajor : family^2*eps^2 ≤ L^(-Dgoal) := by
    calc
      _ ≤ L^(2*E)*eps^2 :=
        mul_le_mul_of_nonneg_right hFamilySq (sq_nonneg _)
      _ ≤ L^(2*E)*L^(2*Ck-2*Bmaj) :=
        mul_le_mul_of_nonneg_left hEpsBound
          (Real.rpow_nonneg hLnn _)
      _ = L^(2*E+(2*Ck-2*Bmaj)) :=
        (Real.rpow_add hLpos (2*E) (2*Ck-2*Bmaj)).symm
      _ ≤ L^(-Dgoal) :=
        Real.rpow_le_rpow_of_exponent_le hL hExpMajor
  have hTermMinor :
      family^2*L^(-Bout) ≤ L^(-Dgoal) := by
    calc
      _ ≤ L^(2*E)*L^(-Bout) :=
        mul_le_mul_of_nonneg_right hFamilySq
          (Real.rpow_nonneg hLnn _)
      _ = L^(2*E-Bout) := by
        rw [sub_eq_add_neg,Real.rpow_add hLpos]
      _ ≤ L^(-Dgoal) :=
        Real.rpow_le_rpow_of_exponent_le hL hExpMinor
  have hTermBad :
      family^2*L^(-(2*Bmaj)) ≤ L^(-Dgoal) := by
    calc
      _ ≤ L^(2*E)*L^(-(2*Bmaj)) :=
        mul_le_mul_of_nonneg_right hFamilySq
          (Real.rpow_nonneg hLnn _)
      _ = L^(2*E-2*Bmaj) := by
        rw [sub_eq_add_neg,Real.rpow_add hLpos]
      _ ≤ L^(-Dgoal) :=
        Real.rpow_le_rpow_of_exponent_le hL hExpBad
  have hA := mul_le_mul_of_nonneg_left
    hTermMajor (by norm_num : (0:ℝ) ≤ 4)
  have hB := mul_le_mul_of_nonneg_left
    hTermMinor (by norm_num : (0:ℝ) ≤ 288000)
  have hC := mul_le_mul_of_nonneg_left
    hTermBad (by norm_num : (0:ℝ) ≤ 2)
  dsimp only
  calc
    family^2*(2*(2*(eps^2+72000*L^(-Bout))+
      L^(-(2*Bmaj)))) =
      4*(family^2*eps^2)+
      288000*(family^2*L^(-Bout))+
      2*(family^2*L^(-(2*Bmaj))) := by ring
    _ ≤ 4*L^(-Dgoal)+288000*L^(-Dgoal)+
        2*L^(-Dgoal) :=
      add_le_add (add_le_add hA hB) hC
    _ = 288006*L^(-Dgoal) := by ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueC191FixedFloorPower -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 6500000

/-- The actual original C191 constant K is chosen BEFORE the
large logarithmic scale L. Whenever the original harmonic
normalization floor Vmin is bounded below by a fixed positive
value, its prefactor 3K/Vmin+2 is EVENTUALLY bounded by L^Ck
for every fixed positive exponent Ck.
No extra analytic hypothesis on K or prime groups is used.
The lower floor is essential: allowing Vmin to approach zero
arbitrarily with L would invalidate this conclusion. -/
theorem eventually_source_original_C191_fixed_floor_power434
    (K vFloor Ck : ℝ)
    (hK : 0 ≤ K) (hFloor : 0 < vFloor) (hCk : 0 < Ck) :
    ∀ᶠ L : ℝ in atTop, ∀ Vmin : ℝ,
      vFloor ≤ Vmin →
      3*(K/Vmin)+2 ≤ L^Ck := by
  have hEventually :=
    (tendsto_rpow_atTop hCk).eventually
      (eventually_ge_atTop (3*(K/vFloor)+2))
  filter_upwards [hEventually] with L hPower Vmin hVmin
  have hRatio : K/Vmin ≤ K/vFloor :=
    div_le_div_of_nonneg_left hK hFloor hVmin
  linarith
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueSmallBigFourSignsFamily -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 11000000

/-- C-DIRECTION FULL ORIGINAL SIGNED ν-family C191/C6/discarded
L² estimate persists with ALL FOUR actual independent endpoint
parity choices (00,01,10,11). Each term is weighted by the
TRUE small-plus-BIG shared labelled-slot parity factor
(-1)^(sum_g |shared_original_slots(g,ν)|) when its endpoint
is twisted, rather than by a pattern-independent dummy sign.
The full harmonic prime law, arbitrary mark-sensitive endpoint
tests, actual ν index and Fourier/Mellin phase are retained.
All original SMALL groups contribute J common shared slots.
The per-ν arithmetic C191/C6 estimates are a PREVIOUSLY
PROVED named input hPerNu. This does NOT identify all four
signed physical families with the same original ideal residual:
independent signed B transference is a separate obligation. -/
theorem source_original_true_SMALL_BIG_four_endpoint_physical_family_L2_sum434
    {ι G : Type} [Fintype ι] [DecidableEq ι]
      [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (d : SourceComparisonData434 ι G cfg x L Y Hprime)
    (blockA blockB : Finset G)
    (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ)
    (hA hB : SourceOriginalProbePattern434 G m → ℝ)
    (xi ζ theta : ℝ) (k : ℤ)
    (sourceTest targetTest :
      (ν : SourceOriginalProbePattern434 G m) →
      SourceOriginalVariableBIGState434
        (fun g : G => {p : ℕ // p ∈ d.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ)
    (save : ℝ) (hSave : 0 ≤ save)
    (hES : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
      0 ≤ sourceOriginalTrueNuSignedFullPhysicalEnergy434
        d J ell m hmJ sourceTest ν ∧
      sourceOriginalTrueNuSignedFullPhysicalEnergy434
        d J ell m hmJ sourceTest ν ≤ 1)
    (hET : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
      0 ≤ sourceOriginalTrueNuSignedFullPhysicalEnergy434
        d J ell m hmJ targetTest ν ∧
      sourceOriginalTrueNuSignedFullPhysicalEnergy434
        d J ell m hmJ targetTest ν ≤ 1)
    (hPerNu : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
      ‖sourceOriginalTrueNuSignedFullPhysicalPairing434
        d J ell m hmJ Q hA hB xi ζ theta k
        sourceTest targetTest ν‖^2 ≤
      save *
        sourceOriginalTrueNuSignedFullPhysicalEnergy434
          d J ell m hmJ sourceTest ν *
        sourceOriginalTrueNuSignedFullPhysicalEnergy434
          d J ell m hmJ targetTest ν)
    (epsSrc epsTgt : Bool) :
    let shared := fun ν : SourceOriginalProbePattern434 G m =>
      ((Fintype.card ι)*J) + ∑ g : G,
        (sourceOriginalProbeSharedSlots434 J ell m hmJ ν g).card
    let sign := fun ν : SourceOriginalProbePattern434 G m =>
      (if epsSrc then (-1:ℂ)^(shared ν) else 1) *
      (if epsTgt then (-1:ℂ)^(shared ν) else 1)
    ‖∑ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
      sign ν * sourceOriginalTrueNuSignedFullPhysicalPairing434
        d J ell m hmJ Q hA hB xi ζ theta k
        sourceTest targetTest ν‖^2 ≤
      ((2^(m*(blockA.card+blockB.card)):ℝ)^2)*save := by
  classical
  let shared := fun ν : SourceOriginalProbePattern434 G m =>
    ((Fintype.card ι)*J) + ∑ g : G,
      (sourceOriginalProbeSharedSlots434 J ell m hmJ ν g).card
  let sign := fun ν : SourceOriginalProbePattern434 G m =>
    (if epsSrc then (-1:ℂ)^(shared ν) else 1) *
    (if epsTgt then (-1:ℂ)^(shared ν) else 1)
  have hUnit (ν : SourceOriginalProbePattern434 G m)
      (hν : ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m) :
      ‖sign ν‖ = 1 := by
    have hPower : ‖(-1:ℂ)^(shared ν)‖ = 1 := by simp
    dsimp only [sign]
    cases epsSrc <;> cases epsTgt
    all_goals simp [norm_mul,hPower]
  have hh := source_original_true_all_nu_physical_unit_sign_L2_sum434
    d blockA blockB J ell m hmJ Q hA hB xi ζ theta k
    sourceTest targetTest save hSave
    sign hUnit hES hET hPerNu
  simpa only [shared,sign] using hh
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueAllNuSmallBigFourEndpoint -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 20000000

/-- FOUR-ENDPOINT signed original ν SOURCE03 RAW-minus-Knu
full-free-mark physical Fourier/Mellin residuals summed with the
true two-block pattern combinatorics, with NO primitive character
multiplicity factor or hidden spectral hMinor premise.
The REAL ordered small/BIG prime group geometry and source03
canonical mesh, C191+C6 and discarded inputs are all explicit:
  squared norm of sum_ν <= 2^(2m(sA+sB)) *
    2*(2*(eps_C191²+72000 L^-Bout)+L^-2Bmaj).
For each ν the actual endpoint tests are arbitrary complex full
mark-sensitive L2-normalized laws; the same original source
prime groups, primitive conductor family and Fourier/Mellin phase
are retained. This is still the SUM OF physical ν signed errors;
the exact identification with the raw+comparison residual of the
paper requires a separate shared-dilation/RAW baseline identity.
This theorem controls all four signed physical ν comparison
residuals only; independent signed ideal B transference and
RAW-baseline alignment are NOT established. Green64 is OPEN. -/
theorem eventually_source_original_true_ALL_nu_SMALL_BIG_FOUR_ENDPOINT_signed434
    (cfg : SourceComparisonFixed434)
    (Cq CxiNat Cs C4 : ℕ) (gamma d Bmaj : ℝ)
    (hgamma : 0 < gamma) (hd : 0 ≤ d) (hBmaj : 0 < Bmaj)
    (D Bsave : ℝ) (hD : 0 ≤ D)
    (C : ℕ)
    (hExponent : cfg.C0 *
      Real.log (((cfg.tmax.factorial:ℕ):ℝ) *
        (max (1:ℝ) cfg.vmin⁻¹)^cfg.tmax) ≤ (C:ℝ))
    (hSaving : Bsave+2*(C:ℝ) ≤ D)
    (Cchar CxiReal Bgoal : ℝ)
    (hCchar : 0 ≤ Cchar) (hCxiReal : 0 ≤ CxiReal)
    (hExpBudget : Bgoal+8*(Cchar+CxiReal) ≤ Bsave)
    (Aarc : ℝ) (hAarc : (1/2:ℝ) < Aarc)
    (hArc : Aarc+(D+1) ≤ cfg.Carc)
    (M Bout : ℝ) (hM : 0 ≤ M)
    (hXiExponent :
      2*Bmaj+d+(Bmaj+(((4*Cq+C4:ℕ):ℝ)))+1 ≤ (CxiNat:ℝ))
    (hMinorExponent :
      Bout+2*(d+(Bmaj+(((4*Cq+C4:ℕ):ℝ)))+1) ≤ Bgoal) :
    ∃ K Y : ℝ, 0 ≤ K ∧ ∀ᶠ L : ℝ in atTop,
    ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
      [Fintype β] [DecidableEq β]
    (x Ydata Hprime : ℝ)
    (data : SourceComparisonData434 ι β cfg x L Ydata Hprime)
    (loS hiS : ι → ℕ) (loB hiB : β → ℕ)
    (hSmallSubset : ∀ i, data.Ts i ⊆
       sourceOriginalActualPrimeBand434 (loS i) (hiS i))
    (hBigFull : ∀ j, data.Tb j =
       sourceOriginalActualPrimeBand434 (loB j) (hiB j))
    (hSmallOrder : ∀ i j : ι, i ≠ j →
       hiS i ≤ loS j ∨ hiS j ≤ loS i)
    (hBigOrder : ∀ i j : β, i ≠ j →
       hiB i ≤ loB j ∨ hiB j ≤ loB i)
    (hTsUpper : ∀ i : ι, ∀ p ∈ data.Ts i,
       (p:ℝ) ≤ Real.exp (L^cfg.bexp))
    (hVbig : ∀ g : β, data.Vbig g =
       ∑ p ∈ data.Tb g, 1/(p:ℝ))
    (blockA blockB : Finset β) (hDisjoint : Disjoint blockA blockB)
    (m Qchar : ℕ) (hm : m ≤ cfg.tmax)
    (J ell : ℕ) (hmJ : m ≤ J)
    (hTbLower : ∀ g : β, ∀ p ∈ data.Tb g,
      Real.exp (L^cfg.cexp) ≤ (p:ℝ))
    (hAvar hBvar : SourceOriginalProbePattern434 β m → ℝ)
    (hhA : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m, 0 < hAvar ν ∧ hAvar ν ≤ 1)
    (hhB : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m, 0 < hBvar ν ∧ hBvar ν ≤ 1)
    (xi : ℝ) (hxi : 0 < xi)
    (hQpoly : (Qchar:ℝ) ≤ L^Cchar)
    (hXipoly : xi⁻¹ ≤ L^CxiReal)
    (hQpositive : 0 < Qchar)
    (Vmin : ℝ) (hVmin : 0 < Vmin)
    (hMass : ∀ g : β, Vmin ≤ data.Vbig g)
    (hBigLower : ∀ g : β, Qchar^2 ≤ loB g)
    (hL : 192 ≤ L)
    (hBigUpper : ∀ g : β, (hiB g:ℝ) ≤ Real.exp (L^d))
    (hLdyad : ((Real.log (2:ℝ))⁻¹+1) ≤ L)
    (hQ : (Qchar:ℝ) ≤ L^Cq)
    (hLoOne : ∀ g : β, 1 ≤ loB g)
    (hLoLeHi : ∀ g : β, loB g ≤ hiB g)
    (hLoLarge : ∀ g : β,
      Real.exp (L^gamma) ≤ ((loB g+1:ℕ):ℝ))
    (hYbound : ∀ g : β, Y ≤ ((loB g+1:ℕ):ℝ))
    (ζ theta : ℝ) (k : ℤ) (hk : k ≠ 0)
    (S : ℝ) (hS : 0 ≤ S) (hSscale : S ≤ L^Cs)
    (hQchar : k.natAbs*Nat.ceil (L^(D+1)) ≤ Qchar)
    (hBudget : 3*(((k.natAbs*Nat.ceil (L^(D+1)):ℕ):ℝ)) *
      |(k:ℝ)| *L^cfg.Carc ≤ 2*S)
    (hC4 : (Cs:ℝ)+1 ≤ (C4:ℝ))
    (hDeltaLe : (K/Vmin)*L^(-(Bmaj+(Cq:ℝ))) ≤ 1)
    (hZeta : |ζ| ≤ L^C4)
    (hLMesh : 16*(M+1) ≤ L)
    (hCount : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m,
      ((Fintype.card ν.1+Fintype.card ν.2:ℕ):ℝ) ≤ M)
    (hMeshA : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m,
      hAvar ν = L^(-(Bmaj+(((4*Cq+C4:ℕ):ℝ))))/2)
    (hMeshB : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m,
      hBvar ν = L^(-(Bmaj+(((4*Cq+C4:ℕ):ℝ))))/2)
    (hXiChoice :
      xi = L^(-(2*Bmaj+d+(Bmaj+(((4*Cq+C4:ℕ):ℝ)))))/
        (16*(M+1)))
    (sourceTest targetTest :
      (ν : SourceOriginalProbePattern434 β m) →
      SourceOriginalVariableBIGState434
        (fun g : β => {p : ℕ // p ∈ data.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ)
    (hES : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m,
      0 ≤ sourceOriginalTrueNuSignedFullPhysicalEnergy434
        data J ell m hmJ sourceTest ν ∧
      sourceOriginalTrueNuSignedFullPhysicalEnergy434
        data J ell m hmJ sourceTest ν ≤ 1)
    (hET : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m,
      0 ≤ sourceOriginalTrueNuSignedFullPhysicalEnergy434
        data J ell m hmJ targetTest ν ∧
      sourceOriginalTrueNuSignedFullPhysicalEnergy434
        data J ell m hmJ targetTest ν ≤ 1)
    (epsSrc epsTgt : Bool),
    let family := sourceOriginalTwoBlockProbePatterns434
      blockA blockB m
    let eps : ℝ := (3*(K/Vmin)+2)*L^(-Bmaj)
    let budget : ℝ :=
      2*(2*(eps^2+72000*L^(-Bout))+L^(-(2*Bmaj)))
    let shared := fun ν : SourceOriginalProbePattern434 β m =>
      ((Fintype.card ι)*J) + ∑ g : β,
        (sourceOriginalProbeSharedSlots434 J ell m hmJ ν g).card
    let sign := fun ν : SourceOriginalProbePattern434 β m =>
      (if epsSrc then (-1:ℂ)^(shared ν) else 1) *
      (if epsTgt then (-1:ℂ)^(shared ν) else 1)
    ‖∑ ν ∈ family,
      sign ν * sourceOriginalTrueNuSignedFullPhysicalPairing434
        data J ell m hmJ Qchar hAvar hBvar xi ζ theta k
        sourceTest targetTest ν‖^2 ≤
      ((2^(m*(blockA.card+blockB.card)):ℝ)^2)*budget := by
  obtain ⟨K,Y,hK,hCore⟩ :=
    eventually_source_original_true_ANY_nu_CANONICAL_ordered_bands_signed434
      cfg Cq CxiNat Cs C4 gamma d Bmaj hgamma hd hBmaj
      D Bsave hD C hExponent hSaving
      Cchar CxiReal Bgoal hCchar hCxiReal hExpBudget
      Aarc hAarc hArc M Bout hM hXiExponent hMinorExponent
  refine ⟨K,Y,hK,?_⟩
  filter_upwards [hCore] with L hCoreL
  intro ι β instI instDI instB instDB
    x Ydata Hprime data
    loS hiS loB hiB hSmallSubset hBigFull
    hSmallOrder hBigOrder hTsUpper hVbig
    blockA blockB hDisjoint m Qchar hm J ell hmJ hTbLower
    hAvar hBvar hhA hhB xi hxi hQpoly hXipoly
    hQpositive Vmin hVmin hMass hBigLower
    hL hBigUpper hLdyad hQ
    hLoOne hLoLeHi hLoLarge hYbound
    ζ theta k hk S hS hSscale hQchar hBudget
    hC4 hDeltaLe hZeta hLMesh hCount hMeshA hMeshB
    hXiChoice sourceTest targetTest hES hET epsSrc epsTgt
  classical
  let family := sourceOriginalTwoBlockProbePatterns434 blockA blockB m
  let eps : ℝ := (3*(K/Vmin)+2)*L^(-Bmaj)
  let budget : ℝ := 2*(2*(eps^2+72000*L^(-Bout))+L^(-(2*Bmaj)))
  have hLpos : 0 < L := by linarith
  have hSaveNN : 0 ≤ budget := by
    dsimp only [budget,eps]
    positivity
  have hPerNu (ν : SourceOriginalProbePattern434 β m) (hν : ν ∈ family) :
      ‖sourceOriginalTrueNuSignedFullPhysicalPairing434
        data J ell m hmJ Qchar hAvar hBvar xi ζ theta k
        sourceTest targetTest ν‖^2 ≤
      budget *
      sourceOriginalTrueNuSignedFullPhysicalEnergy434
        data J ell m hmJ sourceTest ν *
      sourceOriginalTrueNuSignedFullPhysicalEnergy434
        data J ell m hmJ targetTest ν := by
    have hPattern :=
      (source_original_two_block_probe_pattern_mem434
        blockA blockB m ν.1 ν.2).mp hν
    obtain ⟨gA,hgA⟩ := hPattern.1
    obtain ⟨gB,hgB⟩ := hPattern.2.2.1
    let iA : ν.1 := ⟨gA,hgA⟩
    let iB : ν.2 := ⟨gB,hgB⟩
    have hh := hCoreL x Ydata Hprime data
      loS hiS loB hiB hSmallSubset hBigFull
      hSmallOrder hBigOrder hTsUpper hVbig
      blockA blockB hDisjoint m Qchar hm J ell hmJ hTbLower
      hAvar hBvar hhA hhB xi hxi hQpoly hXipoly
      ν hν hQpositive Vmin hVmin hMass hBigLower
      hL hBigUpper hLdyad hQ
      iA iB hLoOne hLoLeHi hLoLarge
      (hYbound iA.val.1) (hYbound iB.val.1)
      ζ theta k hk S hS hSscale hQchar hBudget
      hC4 hDeltaLe hZeta hLMesh
      (hCount ν hν) (hMeshA ν hν) (hMeshB ν hν)
      hXiChoice (sourceTest ν) (targetTest ν)
    change
      ‖sourceOriginalTrueNuSignedFullPhysicalPairing434
        data J ell m hmJ Qchar hAvar hBvar xi ζ theta k
        sourceTest targetTest ν‖^2 ≤
      budget *
      sourceOriginalTrueNuSignedFullPhysicalEnergy434
        data J ell m hmJ sourceTest ν *
      sourceOriginalTrueNuSignedFullPhysicalEnergy434
        data J ell m hmJ targetTest ν at hh
    exact hh
  have hFamily :=
    source_original_true_SMALL_BIG_four_endpoint_physical_family_L2_sum434
      data blockA blockB J ell m hmJ Qchar
      hAvar hBvar xi ζ theta k
      sourceTest targetTest budget hSaveNN
      hES hET hPerNu epsSrc epsTgt
  simpa only [family,eps,budget] using hFamily
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueAllNuFourSignPowerSaving -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- Full original SOURCE03 signed ν-family PHYSICAL C191+C6+
discarded weighted L² bound, with explicit ARBITRARILY LARGE
logarithmic saving after ALL genuine ν-pattern summation costs.
For EACH of the four independent endpoint parity channels:
 norm² ≤ 288006 L^(-Dgoal) as soon as the real BIG group count
satisfies the original Cgroup*log L restriction, the original
C191 prefactor 3K/Vmin+2 grows at most L^Ck, and the major/
minor exponent budgets leave sufficient polynomial margin.
No primitive-character cardinality added (Knu already summed
inside each genuine ν operator). Keeps full mark-sensitive
source and target tests and their true harmonic probabilities.
This still assumes explicit source prime-group admissibility
and is NOT an original B transference or Green64 theorem. -/
theorem eventually_source_original_true_ALL_nu_FOUR_SIGNS_log_saving434
    (cfg : SourceComparisonFixed434)
    (Cq CxiNat Cs C4 : ℕ) (gamma d Bmaj : ℝ)
    (hgamma : 0 < gamma) (hd : 0 ≤ d) (hBmaj : 0 < Bmaj)
    (D Bsave : ℝ) (hD : 0 ≤ D)
    (C : ℕ)
    (hExponent : cfg.C0 *
      Real.log (((cfg.tmax.factorial:ℕ):ℝ) *
        (max (1:ℝ) cfg.vmin⁻¹)^cfg.tmax) ≤ (C:ℝ))
    (hSaving : Bsave+2*(C:ℝ) ≤ D)
    (Cchar CxiReal Bgoal : ℝ)
    (hCchar : 0 ≤ Cchar) (hCxiReal : 0 ≤ CxiReal)
    (hExpBudget : Bgoal+8*(Cchar+CxiReal) ≤ Bsave)
    (Aarc : ℝ) (hAarc : (1/2:ℝ) < Aarc)
    (hArc : Aarc+(D+1) ≤ cfg.Carc)
    (M Bout : ℝ) (hM : 0 ≤ M)
    (hXiExponent :
      2*Bmaj+d+(Bmaj+(((4*Cq+C4:ℕ):ℝ)))+1 ≤ (CxiNat:ℝ))
    (hMinorExponent :
      Bout+2*(d+(Bmaj+(((4*Cq+C4:ℕ):ℝ)))+1) ≤ Bgoal)
    (Cgroup Ck Dgoal : ℝ)
    (hCgroup : 0 ≤ Cgroup) (hCk : 0 ≤ Ck) :
    ∃ K Y : ℝ, 0 ≤ K ∧ ∀ᶠ L : ℝ in atTop,
    ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
      [Fintype β] [DecidableEq β]
    (x Ydata Hprime : ℝ)
    (data : SourceComparisonData434 ι β cfg x L Ydata Hprime)
    (loS hiS : ι → ℕ) (loB hiB : β → ℕ)
    (hSmallSubset : ∀ i, data.Ts i ⊆
       sourceOriginalActualPrimeBand434 (loS i) (hiS i))
    (hBigFull : ∀ j, data.Tb j =
       sourceOriginalActualPrimeBand434 (loB j) (hiB j))
    (hSmallOrder : ∀ i j : ι, i ≠ j →
       hiS i ≤ loS j ∨ hiS j ≤ loS i)
    (hBigOrder : ∀ i j : β, i ≠ j →
       hiB i ≤ loB j ∨ hiB j ≤ loB i)
    (hTsUpper : ∀ i : ι, ∀ p ∈ data.Ts i,
       (p:ℝ) ≤ Real.exp (L^cfg.bexp))
    (hVbig : ∀ g : β, data.Vbig g =
       ∑ p ∈ data.Tb g, 1/(p:ℝ))
    (blockA blockB : Finset β) (hDisjoint : Disjoint blockA blockB)
    (m Qchar : ℕ) (hm : m ≤ cfg.tmax)
    (J ell : ℕ) (hmJ : m ≤ J)
    (hTbLower : ∀ g : β, ∀ p ∈ data.Tb g,
      Real.exp (L^cfg.cexp) ≤ (p:ℝ))
    (hAvar hBvar : SourceOriginalProbePattern434 β m → ℝ)
    (hhA : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m, 0 < hAvar ν ∧ hAvar ν ≤ 1)
    (hhB : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m, 0 < hBvar ν ∧ hBvar ν ≤ 1)
    (xi : ℝ) (hxi : 0 < xi)
    (hQpoly : (Qchar:ℝ) ≤ L^Cchar)
    (hXipoly : xi⁻¹ ≤ L^CxiReal)
    (hQpositive : 0 < Qchar)
    (Vmin : ℝ) (hVmin : 0 < Vmin)
    (hMass : ∀ g : β, Vmin ≤ data.Vbig g)
    (hBigLower : ∀ g : β, Qchar^2 ≤ loB g)
    (hL : 192 ≤ L)
    (hBigUpper : ∀ g : β, (hiB g:ℝ) ≤ Real.exp (L^d))
    (hLdyad : ((Real.log (2:ℝ))⁻¹+1) ≤ L)
    (hQ : (Qchar:ℝ) ≤ L^Cq)
    (hLoOne : ∀ g : β, 1 ≤ loB g)
    (hLoLeHi : ∀ g : β, loB g ≤ hiB g)
    (hLoLarge : ∀ g : β,
      Real.exp (L^gamma) ≤ ((loB g+1:ℕ):ℝ))
    (hYbound : ∀ g : β, Y ≤ ((loB g+1:ℕ):ℝ))
    (ζ theta : ℝ) (k : ℤ) (hk : k ≠ 0)
    (S : ℝ) (hS : 0 ≤ S) (hSscale : S ≤ L^Cs)
    (hQchar : k.natAbs*Nat.ceil (L^(D+1)) ≤ Qchar)
    (hBudget : 3*(((k.natAbs*Nat.ceil (L^(D+1)):ℕ):ℝ)) *
      |(k:ℝ)| *L^cfg.Carc ≤ 2*S)
    (hC4 : (Cs:ℝ)+1 ≤ (C4:ℝ))
    (hDeltaLe : (K/Vmin)*L^(-(Bmaj+(Cq:ℝ))) ≤ 1)
    (hZeta : |ζ| ≤ L^C4)
    (hLMesh : 16*(M+1) ≤ L)
    (hCount : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m,
      ((Fintype.card ν.1+Fintype.card ν.2:ℕ):ℝ) ≤ M)
    (hMeshA : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m,
      hAvar ν = L^(-(Bmaj+(((4*Cq+C4:ℕ):ℝ))))/2)
    (hMeshB : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m,
      hBvar ν = L^(-(Bmaj+(((4*Cq+C4:ℕ):ℝ))))/2)
    (hXiChoice :
      xi = L^(-(2*Bmaj+d+(Bmaj+(((4*Cq+C4:ℕ):ℝ)))))/
        (16*(M+1)))
    (sourceTest targetTest :
      (ν : SourceOriginalProbePattern434 β m) →
      SourceOriginalVariableBIGState434
        (fun g : β => {p : ℕ // p ∈ data.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ)
    (hES : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m,
      0 ≤ sourceOriginalTrueNuSignedFullPhysicalEnergy434
        data J ell m hmJ sourceTest ν ∧
      sourceOriginalTrueNuSignedFullPhysicalEnergy434
        data J ell m hmJ sourceTest ν ≤ 1)
    (hET : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m,
      0 ≤ sourceOriginalTrueNuSignedFullPhysicalEnergy434
        data J ell m hmJ targetTest ν ∧
      sourceOriginalTrueNuSignedFullPhysicalEnergy434
        data J ell m hmJ targetTest ν ≤ 1)
    (epsSrc epsTgt : Bool)
    (hGroups : (((blockA.card+blockB.card:ℕ)):ℝ) ≤
      Cgroup*Real.log L)
    (hC191 : 3*(K/Vmin)+2 ≤ L^Ck)
    (hMajorExp :
      Dgoal+2*((m:ℝ)*Cgroup*Real.log 2)+2*Ck ≤ 2*Bmaj)
    (hMinorExp :
      Dgoal+2*((m:ℝ)*Cgroup*Real.log 2) ≤ Bout),
    let family := sourceOriginalTwoBlockProbePatterns434
      blockA blockB m
    let eps : ℝ := (3*(K/Vmin)+2)*L^(-Bmaj)
    let budget : ℝ :=
      2*(2*(eps^2+72000*L^(-Bout))+L^(-(2*Bmaj)))
    let shared := fun ν : SourceOriginalProbePattern434 β m =>
      ((Fintype.card ι)*J) + ∑ g : β,
        (sourceOriginalProbeSharedSlots434 J ell m hmJ ν g).card
    let sign := fun ν : SourceOriginalProbePattern434 β m =>
      (if epsSrc then (-1:ℂ)^(shared ν) else 1) *
      (if epsTgt then (-1:ℂ)^(shared ν) else 1)
    ‖∑ ν ∈ family,
      sign ν * sourceOriginalTrueNuSignedFullPhysicalPairing434
        data J ell m hmJ Qchar hAvar hBvar xi ζ theta k
        sourceTest targetTest ν‖^2 ≤
      288006*L^(-Dgoal) := by
  obtain ⟨K,Y,hK,hCore⟩ :=
    eventually_source_original_true_ALL_nu_SMALL_BIG_FOUR_ENDPOINT_signed434
      cfg Cq CxiNat Cs C4 gamma d Bmaj hgamma hd hBmaj
      D Bsave hD C hExponent hSaving
      Cchar CxiReal Bgoal hCchar hCxiReal hExpBudget
      Aarc hAarc hArc M Bout hM hXiExponent hMinorExponent
  refine ⟨K,Y,hK,?_⟩
  filter_upwards [hCore] with L hCoreL
  intro ι β instI instDI instB instDB
    x Ydata Hprime data
    loS hiS loB hiB hSmallSubset hBigFull
    hSmallOrder hBigOrder hTsUpper hVbig
    blockA blockB hDisjoint m Qchar hm J ell hmJ hTbLower
    hAvar hBvar hhA hhB xi hxi hQpoly hXipoly
    hQpositive Vmin hVmin hMass hBigLower
    hL hBigUpper hLdyad hQ
    hLoOne hLoLeHi hLoLarge hYbound
    ζ theta k hk S hS hSscale hQchar hBudget
    hC4 hDeltaLe hZeta hLMesh hCount hMeshA hMeshB
    hXiChoice sourceTest targetTest hES hET epsSrc epsTgt
    hGroups hC191 hMajorExp hMinorExp
  classical
  let family := sourceOriginalTwoBlockProbePatterns434 blockA blockB m
  let eps : ℝ := (3*(K/Vmin)+2)*L^(-Bmaj)
  let budget : ℝ :=
    2*(2*(eps^2+72000*L^(-Bout))+L^(-(2*Bmaj)))
  let shared := fun ν : SourceOriginalProbePattern434 β m =>
    ((Fintype.card ι)*J) + ∑ g : β,
      (sourceOriginalProbeSharedSlots434 J ell m hmJ ν g).card
  let sign := fun ν : SourceOriginalProbePattern434 β m =>
    (if epsSrc then (-1:ℂ)^(shared ν) else 1) *
    (if epsTgt then (-1:ℂ)^(shared ν) else 1)
  have hOriginal := hCoreL
    x Ydata Hprime data
    loS hiS loB hiB hSmallSubset hBigFull
    hSmallOrder hBigOrder hTsUpper hVbig
    blockA blockB hDisjoint m Qchar hm J ell hmJ hTbLower
    hAvar hBvar hhA hhB xi hxi hQpoly hXipoly
    hQpositive Vmin hVmin hMass hBigLower
    hL hBigUpper hLdyad hQ
    hLoOne hLoLeHi hLoLarge hYbound
    ζ theta k hk S hS hSscale hQchar hBudget
    hC4 hDeltaLe hZeta hLMesh hCount hMeshA hMeshB
    hXiChoice sourceTest targetTest hES hET epsSrc epsTgt
  have hAbsorb :=
    source_original_true_all_nu_FULL_sign_loss_absorb434
      blockA blockB m L Cgroup Ck Bmaj Bout Dgoal K Vmin
      (by linarith : 1 ≤ L) hCgroup hCk
      hGroups hK hVmin hC191 hMajorExp hMinorExp
  change
    ((2^(m*(blockA.card+blockB.card)):ℝ)^2)*budget ≤
      288006*L^(-Dgoal) at hAbsorb
  have hReal :
      ‖∑ ν ∈ family,
        sign ν * sourceOriginalTrueNuSignedFullPhysicalPairing434
          data J ell m hmJ Qchar hAvar hBvar xi ζ theta k
          sourceTest targetTest ν‖^2 ≤
        ((2^(m*(blockA.card+blockB.card)):ℝ)^2)*budget := by
    simpa only [family,eps,budget,shared,sign] using hOriginal
  have hFinal := hReal.trans hAbsorb
  simpa only [family,eps,budget,shared,sign] using hFinal
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueAllNuFourSignEventualSaving -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- Full original SOURCE03 signed ν-family PHYSICAL C191+C6+
discarded weighted L² bound, with explicit ARBITRARILY LARGE
logarithmic saving after ALL genuine ν-pattern summation costs.
For EACH of the four independent endpoint parity channels:
 norm² ≤ 288006 L^(-Dgoal) as soon as the real BIG group count
satisfies the original Cgroup*log L restriction, the original
C191 prefactor 3K/Vmin+2 grows at most L^Ck, and the major/
minor exponent budgets leave sufficient polynomial margin.
No primitive-character cardinality added (Knu already summed
inside each genuine ν operator). Keeps full mark-sensitive
source and target tests and their true harmonic probabilities.
This still assumes explicit source prime-group admissibility
and is NOT an original B transference or Green64 theorem. -/
theorem eventually_source_original_true_ALL_nu_FOUR_SIGNS_FIXED_FLOOR_saving434
    (cfg : SourceComparisonFixed434)
    (Cq CxiNat Cs C4 : ℕ) (gamma d Bmaj : ℝ)
    (hgamma : 0 < gamma) (hd : 0 ≤ d) (hBmaj : 0 < Bmaj)
    (D Bsave : ℝ) (hD : 0 ≤ D)
    (C : ℕ)
    (hExponent : cfg.C0 *
      Real.log (((cfg.tmax.factorial:ℕ):ℝ) *
        (max (1:ℝ) cfg.vmin⁻¹)^cfg.tmax) ≤ (C:ℝ))
    (hSaving : Bsave+2*(C:ℝ) ≤ D)
    (Cchar CxiReal Bgoal : ℝ)
    (hCchar : 0 ≤ Cchar) (hCxiReal : 0 ≤ CxiReal)
    (hExpBudget : Bgoal+8*(Cchar+CxiReal) ≤ Bsave)
    (Aarc : ℝ) (hAarc : (1/2:ℝ) < Aarc)
    (hArc : Aarc+(D+1) ≤ cfg.Carc)
    (M Bout : ℝ) (hM : 0 ≤ M)
    (hXiExponent :
      2*Bmaj+d+(Bmaj+(((4*Cq+C4:ℕ):ℝ)))+1 ≤ (CxiNat:ℝ))
    (hMinorExponent :
      Bout+2*(d+(Bmaj+(((4*Cq+C4:ℕ):ℝ)))+1) ≤ Bgoal)
    (Cgroup Ck Dgoal : ℝ)
    (hCgroup : 0 ≤ Cgroup) (hCk : 0 < Ck) :
    ∃ K Y : ℝ, 0 ≤ K ∧ ∀ᶠ L : ℝ in atTop,
    ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
      [Fintype β] [DecidableEq β]
    (x Ydata Hprime : ℝ)
    (data : SourceComparisonData434 ι β cfg x L Ydata Hprime)
    (loS hiS : ι → ℕ) (loB hiB : β → ℕ)
    (hSmallSubset : ∀ i, data.Ts i ⊆
       sourceOriginalActualPrimeBand434 (loS i) (hiS i))
    (hBigFull : ∀ j, data.Tb j =
       sourceOriginalActualPrimeBand434 (loB j) (hiB j))
    (hSmallOrder : ∀ i j : ι, i ≠ j →
       hiS i ≤ loS j ∨ hiS j ≤ loS i)
    (hBigOrder : ∀ i j : β, i ≠ j →
       hiB i ≤ loB j ∨ hiB j ≤ loB i)
    (hTsUpper : ∀ i : ι, ∀ p ∈ data.Ts i,
       (p:ℝ) ≤ Real.exp (L^cfg.bexp))
    (hVbig : ∀ g : β, data.Vbig g =
       ∑ p ∈ data.Tb g, 1/(p:ℝ))
    (blockA blockB : Finset β) (hDisjoint : Disjoint blockA blockB)
    (m Qchar : ℕ) (hm : m ≤ cfg.tmax)
    (J ell : ℕ) (hmJ : m ≤ J)
    (hTbLower : ∀ g : β, ∀ p ∈ data.Tb g,
      Real.exp (L^cfg.cexp) ≤ (p:ℝ))
    (hAvar hBvar : SourceOriginalProbePattern434 β m → ℝ)
    (hhA : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m, 0 < hAvar ν ∧ hAvar ν ≤ 1)
    (hhB : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m, 0 < hBvar ν ∧ hBvar ν ≤ 1)
    (xi : ℝ) (hxi : 0 < xi)
    (hQpoly : (Qchar:ℝ) ≤ L^Cchar)
    (hXipoly : xi⁻¹ ≤ L^CxiReal)
    (hQpositive : 0 < Qchar)
    (Vmin : ℝ) (hVmin : 0 < Vmin)
    (hVFloor : cfg.vmin ≤ Vmin)
    (hMass : ∀ g : β, Vmin ≤ data.Vbig g)
    (hBigLower : ∀ g : β, Qchar^2 ≤ loB g)
    (hL : 192 ≤ L)
    (hBigUpper : ∀ g : β, (hiB g:ℝ) ≤ Real.exp (L^d))
    (hLdyad : ((Real.log (2:ℝ))⁻¹+1) ≤ L)
    (hQ : (Qchar:ℝ) ≤ L^Cq)
    (hLoOne : ∀ g : β, 1 ≤ loB g)
    (hLoLeHi : ∀ g : β, loB g ≤ hiB g)
    (hLoLarge : ∀ g : β,
      Real.exp (L^gamma) ≤ ((loB g+1:ℕ):ℝ))
    (hYbound : ∀ g : β, Y ≤ ((loB g+1:ℕ):ℝ))
    (ζ theta : ℝ) (k : ℤ) (hk : k ≠ 0)
    (S : ℝ) (hS : 0 ≤ S) (hSscale : S ≤ L^Cs)
    (hQchar : k.natAbs*Nat.ceil (L^(D+1)) ≤ Qchar)
    (hBudget : 3*(((k.natAbs*Nat.ceil (L^(D+1)):ℕ):ℝ)) *
      |(k:ℝ)| *L^cfg.Carc ≤ 2*S)
    (hC4 : (Cs:ℝ)+1 ≤ (C4:ℝ))
    (hDeltaLe : (K/Vmin)*L^(-(Bmaj+(Cq:ℝ))) ≤ 1)
    (hZeta : |ζ| ≤ L^C4)
    (hLMesh : 16*(M+1) ≤ L)
    (hCount : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m,
      ((Fintype.card ν.1+Fintype.card ν.2:ℕ):ℝ) ≤ M)
    (hMeshA : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m,
      hAvar ν = L^(-(Bmaj+(((4*Cq+C4:ℕ):ℝ))))/2)
    (hMeshB : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m,
      hBvar ν = L^(-(Bmaj+(((4*Cq+C4:ℕ):ℝ))))/2)
    (hXiChoice :
      xi = L^(-(2*Bmaj+d+(Bmaj+(((4*Cq+C4:ℕ):ℝ)))))/
        (16*(M+1)))
    (sourceTest targetTest :
      (ν : SourceOriginalProbePattern434 β m) →
      SourceOriginalVariableBIGState434
        (fun g : β => {p : ℕ // p ∈ data.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ)
    (hES : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m,
      0 ≤ sourceOriginalTrueNuSignedFullPhysicalEnergy434
        data J ell m hmJ sourceTest ν ∧
      sourceOriginalTrueNuSignedFullPhysicalEnergy434
        data J ell m hmJ sourceTest ν ≤ 1)
    (hET : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m,
      0 ≤ sourceOriginalTrueNuSignedFullPhysicalEnergy434
        data J ell m hmJ targetTest ν ∧
      sourceOriginalTrueNuSignedFullPhysicalEnergy434
        data J ell m hmJ targetTest ν ≤ 1)
    (epsSrc epsTgt : Bool)
    (hGroups : (((blockA.card+blockB.card:ℕ)):ℝ) ≤
      Cgroup*Real.log L)
    (hMajorExp :
      Dgoal+2*((m:ℝ)*Cgroup*Real.log 2)+2*Ck ≤ 2*Bmaj)
    (hMinorExp :
      Dgoal+2*((m:ℝ)*Cgroup*Real.log 2) ≤ Bout),
    let family := sourceOriginalTwoBlockProbePatterns434
      blockA blockB m
    let eps : ℝ := (3*(K/Vmin)+2)*L^(-Bmaj)
    let budget : ℝ :=
      2*(2*(eps^2+72000*L^(-Bout))+L^(-(2*Bmaj)))
    let shared := fun ν : SourceOriginalProbePattern434 β m =>
      ((Fintype.card ι)*J) + ∑ g : β,
        (sourceOriginalProbeSharedSlots434 J ell m hmJ ν g).card
    let sign := fun ν : SourceOriginalProbePattern434 β m =>
      (if epsSrc then (-1:ℂ)^(shared ν) else 1) *
      (if epsTgt then (-1:ℂ)^(shared ν) else 1)
    ‖∑ ν ∈ family,
      sign ν * sourceOriginalTrueNuSignedFullPhysicalPairing434
        data J ell m hmJ Qchar hAvar hBvar xi ζ theta k
        sourceTest targetTest ν‖^2 ≤
      288006*L^(-Dgoal) := by
  obtain ⟨K,Y,hK,hCore⟩ :=
    eventually_source_original_true_ALL_nu_FOUR_SIGNS_log_saving434
      cfg Cq CxiNat Cs C4 gamma d Bmaj hgamma hd hBmaj
      D Bsave hD C hExponent hSaving
      Cchar CxiReal Bgoal hCchar hCxiReal hExpBudget
      Aarc hAarc hArc M Bout hM hXiExponent hMinorExponent
      Cgroup Ck Dgoal hCgroup hCk.le
  refine ⟨K,Y,hK,?_⟩
  have hPrefactor :=
    eventually_source_original_C191_fixed_floor_power434
      K cfg.vmin Ck hK cfg.hv hCk
  filter_upwards [hCore,hPrefactor] with L hCoreL hPrefL
  intro ι β instI instDI instB instDB
    x Ydata Hprime data
    loS hiS loB hiB hSmallSubset hBigFull
    hSmallOrder hBigOrder hTsUpper hVbig
    blockA blockB hDisjoint m Qchar hm J ell hmJ hTbLower
    hAvar hBvar hhA hhB xi hxi hQpoly hXipoly
    hQpositive Vmin hVmin hVFloor hMass hBigLower
    hL hBigUpper hLdyad hQ
    hLoOne hLoLeHi hLoLarge hYbound
    ζ theta k hk S hS hSscale hQchar hBudget
    hC4 hDeltaLe hZeta hLMesh hCount hMeshA hMeshB
    hXiChoice sourceTest targetTest hES hET epsSrc epsTgt
    hGroups hMajorExp hMinorExp
  classical
  let family := sourceOriginalTwoBlockProbePatterns434 blockA blockB m
  let eps : ℝ := (3*(K/Vmin)+2)*L^(-Bmaj)
  let budget : ℝ :=
    2*(2*(eps^2+72000*L^(-Bout))+L^(-(2*Bmaj)))
  let shared := fun ν : SourceOriginalProbePattern434 β m =>
    ((Fintype.card ι)*J) + ∑ g : β,
      (sourceOriginalProbeSharedSlots434 J ell m hmJ ν g).card
  let sign := fun ν : SourceOriginalProbePattern434 β m =>
    (if epsSrc then (-1:ℂ)^(shared ν) else 1) *
    (if epsTgt then (-1:ℂ)^(shared ν) else 1)
  have hOriginal := hCoreL
    x Ydata Hprime data
    loS hiS loB hiB hSmallSubset hBigFull
    hSmallOrder hBigOrder hTsUpper hVbig
    blockA blockB hDisjoint m Qchar hm J ell hmJ hTbLower
    hAvar hBvar hhA hhB xi hxi hQpoly hXipoly
    hQpositive Vmin hVmin hMass hBigLower
    hL hBigUpper hLdyad hQ
    hLoOne hLoLeHi hLoLarge hYbound
    ζ theta k hk S hS hSscale hQchar hBudget
    hC4 hDeltaLe hZeta hLMesh hCount hMeshA hMeshB
    hXiChoice sourceTest targetTest hES hET epsSrc epsTgt
    hGroups (hPrefL Vmin hVFloor) hMajorExp hMinorExp
  simpa only [family,eps,budget,shared,sign] using hOriginal
end Green64Analytic.CorrelationSquare

end

/-! ## PhysicalC191CharacterwiseRMS -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- The original arithmetic C191+C6 signed residual, with *literal*
mark-sensitive outer χ twist applied to BOTH physical endpoints independently
for each character modulo |k|, is bounded BEFORE averaging any characters.
Then the complete (+,-,-,+)/4 projector is formed BEFORE the χ RMS square.
No 1/φ(|k|) loss. This is C191 signed RAW-minus-Knu residual, NOT the
primitive component or an identification with sourceNativePrimeCore. -/
theorem eventually_source_original_B434_true_ALL_nu_characterwise_C191_projected_RMS434
    (cfg : SourceComparisonFixed434)
    (Cq CxiNat Cs C4 : ℕ) (gamma d Bmaj : ℝ)
    (hgamma : 0 < gamma) (hd : 0 ≤ d) (hBmaj : 0 < Bmaj)
    (D Bsave : ℝ) (hD : 0 ≤ D)
    (C : ℕ)
    (hExponent : cfg.C0 *
      Real.log (((cfg.tmax.factorial:ℕ):ℝ) *
        (max (1:ℝ) cfg.vmin⁻¹)^cfg.tmax) ≤ (C:ℝ))
    (hSaving : Bsave+2*(C:ℝ) ≤ D)
    (Cchar CxiReal Bgoal : ℝ)
    (hCchar : 0 ≤ Cchar) (hCxiReal : 0 ≤ CxiReal)
    (hExpBudget : Bgoal+8*(Cchar+CxiReal) ≤ Bsave)
    (Aarc : ℝ) (hAarc : (1/2:ℝ) < Aarc)
    (hArc : Aarc+(D+1) ≤ cfg.Carc)
    (M Bout : ℝ) (hM : 0 ≤ M)
    (hXiExponent :
      2*Bmaj+d+(Bmaj+(((4*Cq+C4:ℕ):ℝ)))+1 ≤ (CxiNat:ℝ))
    (hMinorExponent :
      Bout+2*(d+(Bmaj+(((4*Cq+C4:ℕ):ℝ)))+1) ≤ Bgoal)
    (Cgroup Ck Dgoal : ℝ)
    (hCgroup : 0 ≤ Cgroup) (hCk : 0 < Ck) :
    ∃ K Y : ℝ, 0 ≤ K ∧ ∀ᶠ L : ℝ in atTop,
    ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
      [Fintype β] [DecidableEq β]
    (x Ydata Hprime : ℝ)
    (data : SourceComparisonData434 ι β cfg x L Ydata Hprime)
    (loS hiS : ι → ℕ) (loB hiB : β → ℕ)
    (hSmallSubset : ∀ i, data.Ts i ⊆
       sourceOriginalActualPrimeBand434 (loS i) (hiS i))
    (hBigFull : ∀ j, data.Tb j =
       sourceOriginalActualPrimeBand434 (loB j) (hiB j))
    (hSmallOrder : ∀ i j : ι, i ≠ j →
       hiS i ≤ loS j ∨ hiS j ≤ loS i)
    (hBigOrder : ∀ i j : β, i ≠ j →
       hiB i ≤ loB j ∨ hiB j ≤ loB i)
    (hTsUpper : ∀ i : ι, ∀ p ∈ data.Ts i,
       (p:ℝ) ≤ Real.exp (L^cfg.bexp))
    (hVbig : ∀ g : β, data.Vbig g =
       ∑ p ∈ data.Tb g, 1/(p:ℝ))
    (blockA blockB : Finset β) (hDisjoint : Disjoint blockA blockB)
    (m Qchar : ℕ) (hm : m ≤ cfg.tmax)
    (J ell : ℕ) (hmJ : m ≤ J)
    (hTbLower : ∀ g : β, ∀ p ∈ data.Tb g,
      Real.exp (L^cfg.cexp) ≤ (p:ℝ))
    (hAvar hBvar : SourceOriginalProbePattern434 β m → ℝ)
    (hhA : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m, 0 < hAvar ν ∧ hAvar ν ≤ 1)
    (hhB : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m, 0 < hBvar ν ∧ hBvar ν ≤ 1)
    (xi : ℝ) (hxi : 0 < xi)
    (hQpoly : (Qchar:ℝ) ≤ L^Cchar)
    (hXipoly : xi⁻¹ ≤ L^CxiReal)
    (hQpositive : 0 < Qchar)
    (Vmin : ℝ) (hVmin : 0 < Vmin)
    (hVFloor : cfg.vmin ≤ Vmin)
    (hMass : ∀ g : β, Vmin ≤ data.Vbig g)
    (hBigLower : ∀ g : β, Qchar^2 ≤ loB g)
    (hL : 192 ≤ L)
    (hBigUpper : ∀ g : β, (hiB g:ℝ) ≤ Real.exp (L^d))
    (hLdyad : ((Real.log (2:ℝ))⁻¹+1) ≤ L)
    (hQ : (Qchar:ℝ) ≤ L^Cq)
    (hLoOne : ∀ g : β, 1 ≤ loB g)
    (hLoLeHi : ∀ g : β, loB g ≤ hiB g)
    (hLoLarge : ∀ g : β,
      Real.exp (L^gamma) ≤ ((loB g+1:ℕ):ℝ))
    (hYbound : ∀ g : β, Y ≤ ((loB g+1:ℕ):ℝ))
    (ζ theta : ℝ) (k : ℤ) (hk : k ≠ 0)
    (S : ℝ) (hS : 0 ≤ S) (hSscale : S ≤ L^Cs)
    (hQchar : k.natAbs*Nat.ceil (L^(D+1)) ≤ Qchar)
    (hBudget : 3*(((k.natAbs*Nat.ceil (L^(D+1)):ℕ):ℝ)) *
      |(k:ℝ)| *L^cfg.Carc ≤ 2*S)
    (hC4 : (Cs:ℝ)+1 ≤ (C4:ℝ))
    (hDeltaLe : (K/Vmin)*L^(-(Bmaj+(Cq:ℝ))) ≤ 1)
    (hZeta : |ζ| ≤ L^C4)
    (hLMesh : 16*(M+1) ≤ L)
    (hCount : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m,
      ((Fintype.card ν.1+Fintype.card ν.2:ℕ):ℝ) ≤ M)
    (hMeshA : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m,
      hAvar ν = L^(-(Bmaj+(((4*Cq+C4:ℕ):ℝ))))/2)
    (hMeshB : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m,
      hBvar ν = L^(-(Bmaj+(((4*Cq+C4:ℕ):ℝ))))/2)
    (hXiChoice :
      xi = L^(-(2*Bmaj+d+(Bmaj+(((4*Cq+C4:ℕ):ℝ)))))/
        (16*(M+1)))
    (baseSource baseTarget :
      (ν : SourceOriginalProbePattern434 β m) →
      SourceOriginalVariableBIGState434
        (fun g : β => {p : ℕ // p ∈ data.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ)
    (hES : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m,
      0 ≤ sourceOriginalTrueNuSignedFullPhysicalEnergy434
        data J ell m hmJ baseSource ν ∧
      sourceOriginalTrueNuSignedFullPhysicalEnergy434
        data J ell m hmJ baseSource ν ≤ 1)
    (hET : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m,
      0 ≤ sourceOriginalTrueNuSignedFullPhysicalEnergy434
        data J ell m hmJ baseTarget ν ∧
      sourceOriginalTrueNuSignedFullPhysicalEnergy434
        data J ell m hmJ baseTarget ν ≤ 1)

    (hGroups : (((blockA.card+blockB.card:ℕ)):ℝ) ≤
      Cgroup*Real.log L)
    (hMajorExp :
      Dgoal+2*((m:ℝ)*Cgroup*Real.log 2)+2*Ck ≤ 2*Bmaj)
    (hMinorExp :
      Dgoal+2*((m:ℝ)*Cgroup*Real.log 2) ≤ Bout),
    let family := sourceOriginalTwoBlockProbePatterns434 blockA blockB m
    let shared := fun ν : SourceOriginalProbePattern434 β m =>
      ((Fintype.card ι)*J) + ∑ g : β,
        (sourceOriginalProbeSharedSlots434 J ell m hmJ ν g).card
    let amplitude := fun (χ : DirichletCharacter ℂ k.natAbs)
        (tw : Bool × Bool) =>
      ∑ ν ∈ family,
        ((if tw.1 then (-1:ℂ)^(shared ν) else 1) *
         (if tw.2 then (-1:ℂ)^(shared ν) else 1)) *
        sourceOriginalTrueNuSignedFullPhysicalPairing434
          data J ell m hmJ Qchar hAvar hBvar xi ζ theta k
          (sourceOriginalB432CharacterSourceTest434 data J ell m hmJ k χ baseSource)
          (sourceOriginalB432CharacterTargetTest434 data J ell m hmJ k χ baseTarget) ν
    (∑ χ : DirichletCharacter ℂ k.natAbs,
       ‖((k.natAbs.totient:ℂ)⁻¹)‖ *
         ‖∑ tw : Bool × Bool,
           sourceOriginalB430ParityCoefficient tw * amplitude χ tw‖^2) ≤
      288006*L^(-Dgoal) := by
  obtain ⟨K,Y,hK,hOriginal⟩ :=
    eventually_source_original_true_ALL_nu_FOUR_SIGNS_FIXED_FLOOR_saving434
      cfg Cq CxiNat Cs C4 gamma d Bmaj hgamma hd hBmaj
      D Bsave hD C hExponent hSaving
      Cchar CxiReal Bgoal hCchar hCxiReal hExpBudget
      Aarc hAarc hArc M Bout hM hXiExponent hMinorExponent
      Cgroup Ck Dgoal hCgroup hCk
  refine ⟨K,Y,hK,?_⟩
  filter_upwards [hOriginal] with L hOrig
  intro ι β instI instDI instB instDB
    x Ydata Hprime data
    loS hiS loB hiB hSmallSubset hBigFull
    hSmallOrder hBigOrder hTsUpper hVbig
    blockA blockB hDisjoint m Qchar hm J ell hmJ hTbLower
    hAvar hBvar hhA hhB xi hxi hQpoly hXipoly
    hQpositive Vmin hVmin hVFloor hMass hBigLower
    hL hBigUpper hLdyad hQ
    hLoOne hLoLeHi hLoLarge hYbound
    ζ theta k hk S hS hSscale hQchar hBudget
    hC4 hDeltaLe hZeta hLMesh hCount hMeshA hMeshB
    hXiChoice baseSource baseTarget hES hET
    hGroups hMajorExp hMinorExp
  dsimp only
  let family := sourceOriginalTwoBlockProbePatterns434 blockA blockB m
  let shared := fun ν : SourceOriginalProbePattern434 β m =>
    ((Fintype.card ι)*J) + ∑ g : β,
      (sourceOriginalProbeSharedSlots434 J ell m hmJ ν g).card
  let amplitude := fun (χ : DirichletCharacter ℂ k.natAbs)
      (tw : Bool × Bool) =>
    ∑ ν ∈ family,
      ((if tw.1 then (-1:ℂ)^(shared ν) else 1) *
       (if tw.2 then (-1:ℂ)^(shared ν) else 1)) *
      sourceOriginalTrueNuSignedFullPhysicalPairing434
        data J ell m hmJ Qchar hAvar hBvar xi ζ theta k
        (sourceOriginalB432CharacterSourceTest434 data J ell m hmJ k χ baseSource)
        (sourceOriginalB432CharacterTargetTest434 data J ell m hmJ k χ baseTarget) ν
  have hSrcEnergy (χ : DirichletCharacter ℂ k.natAbs) :
      ∀ ν ∈ family,
        0 ≤ sourceOriginalTrueNuSignedFullPhysicalEnergy434
          data J ell m hmJ
          (sourceOriginalB432CharacterSourceTest434 data J ell m hmJ k χ baseSource) ν ∧
        sourceOriginalTrueNuSignedFullPhysicalEnergy434
          data J ell m hmJ
          (sourceOriginalB432CharacterSourceTest434 data J ell m hmJ k χ baseSource) ν ≤ 1 := by
    intro ν hν
    exact ⟨source_original_B433_true_physical_energy_nonneg434
      data hVbig J ell m hmJ
      (sourceOriginalB432CharacterSourceTest434 data J ell m hmJ k χ baseSource) ν,
      (source_original_B433_character_source_energy_le434
        data hVbig J ell m hmJ k χ baseSource ν).trans (hES ν hν).2⟩
  have hTgtEnergy (χ : DirichletCharacter ℂ k.natAbs) :
      ∀ ν ∈ family,
        0 ≤ sourceOriginalTrueNuSignedFullPhysicalEnergy434
          data J ell m hmJ
          (sourceOriginalB432CharacterTargetTest434 data J ell m hmJ k χ baseTarget) ν ∧
        sourceOriginalTrueNuSignedFullPhysicalEnergy434
          data J ell m hmJ
          (sourceOriginalB432CharacterTargetTest434 data J ell m hmJ k χ baseTarget) ν ≤ 1 := by
    intro ν hν
    exact ⟨source_original_B433_true_physical_energy_nonneg434
      data hVbig J ell m hmJ
      (sourceOriginalB432CharacterTargetTest434 data J ell m hmJ k χ baseTarget) ν,
      (source_original_B433_character_target_energy_le434
        data hVbig J ell m hmJ k χ baseTarget ν).trans (hET ν hν).2⟩
  let T : ℝ := 288006*L^(-Dgoal)
  have hPer (χ : DirichletCharacter ℂ k.natAbs) (tw : Bool × Bool) :
      ‖amplitude χ tw‖^2 ≤ T := by
    have h := hOrig x Ydata Hprime data
      loS hiS loB hiB hSmallSubset hBigFull
      hSmallOrder hBigOrder hTsUpper hVbig
      blockA blockB hDisjoint m Qchar hm J ell hmJ hTbLower
      hAvar hBvar hhA hhB xi hxi hQpoly hXipoly
      hQpositive Vmin hVmin hVFloor hMass hBigLower
      hL hBigUpper hLdyad hQ
      hLoOne hLoLeHi hLoLarge hYbound
      ζ theta k hk S hS hSscale hQchar hBudget
      hC4 hDeltaLe hZeta hLMesh hCount hMeshA hMeshB
      hXiChoice
      (sourceOriginalB432CharacterSourceTest434 data J ell m hmJ k χ baseSource)
      (sourceOriginalB432CharacterTargetTest434 data J ell m hmJ k χ baseTarget)
      (hSrcEnergy χ) (hTgtEnergy χ) tw.1 tw.2
      hGroups hMajorExp hMinorExp
    simpa only [amplitude,T,family,shared] using h
  have hTnonneg : 0 ≤ T := by
    dsimp [T]
    exact mul_nonneg (by norm_num) (Real.rpow_nonneg (by linarith only [hL]) _)
  have hRootSq : (Real.sqrt T)^2 = T := Real.sq_sqrt hTnonneg
  have hEach (χ : DirichletCharacter ℂ k.natAbs) (tw : Bool × Bool) :
      ‖amplitude χ tw‖ ≤ Real.sqrt T := by
    have hh := hPer χ tw
    have hN := norm_nonneg (amplitude χ tw)
    have hR := Real.sqrt_nonneg T
    nlinarith only [hh,hRootSq,hN,hR]
  have hRMS := source_original_B430_uniform_four_sign_character_RMS434
    k hk amplitude (Real.sqrt T) (Real.sqrt_nonneg _) hEach
  change (∑ χ : DirichletCharacter ℂ k.natAbs,
    ‖((k.natAbs.totient:ℂ)⁻¹)‖ *
      ‖∑ tw : Bool × Bool,
        sourceOriginalB430ParityCoefficient tw * amplitude χ tw‖^2) ≤ T
  simpa only [hRootSq] using hRMS
end Green64Analytic.CorrelationSquare

end

end

/-! ## CofactorCharacterSuperposition -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- Exact bilinear cofactor Fourier superposition. The OUTER character is
applied to the native-style cofactor index m, **not** to a BIG free-prime
product. χ(m) χ̄(n) and α(m) ᾱ(n) emerge in the correct original
source/target order before any square or φ-normalization. No arithmetic
estimate or assertion that F_m equals the native PrimeSlotCore is made. -/
theorem source_original_B435_true_cofactor_character_bilinear434
    {X : Type} [Fintype X]
    (K : Finset ℕ) (alpha : ℕ → ℂ) (q : ℕ)
    (χ : DirichletCharacter ℂ q)
    (H : X → X → ℂ) (F G : ℕ → X → ℂ) :
    (∑ ab : X × X,
       H ab.1 ab.2 *
         star (∑ m ∈ K,
           star (alpha m * χ (m : ZMod q)) * F m ab.1) *
         (∑ n ∈ K,
           star (alpha n * χ (n : ZMod q)) * G n ab.2)) =
    ∑ m ∈ K, ∑ n ∈ K,
      (alpha m * χ (m : ZMod q)) *
        star (alpha n * χ (n : ZMod q)) *
        (∑ ab : X × X,
           H ab.1 ab.2 * star (F m ab.1) * G n ab.2) := by
  classical
  have hpoint (ab : X × X) :
      H ab.1 ab.2 *
         star (∑ m ∈ K,
           star (alpha m * χ (m : ZMod q)) * F m ab.1) *
         (∑ n ∈ K,
           star (alpha n * χ (n : ZMod q)) * G n ab.2) =
      ∑ m ∈ K, ∑ n ∈ K,
        (alpha m * χ (m : ZMod q)) *
          star (alpha n * χ (n : ZMod q)) *
          (H ab.1 ab.2 * star (F m ab.1) * G n ab.2) := by
    simp only [star_sum, star_mul, star_star]
    simp only [Finset.mul_sum, Finset.sum_mul]
    -- Two original cofactor sums arise in target/source order after star.
    -- Swap once, and then use purely commutative complex arithmetic.
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro m hm
    apply Finset.sum_congr rfl
    intro n hn
    ring
  calc
    _ = ∑ ab : X × X, ∑ m ∈ K, ∑ n ∈ K,
      (alpha m * χ (m : ZMod q)) *
        star (alpha n * χ (n : ZMod q)) *
        (H ab.1 ab.2 * star (F m ab.1) * G n ab.2) := by
      apply Finset.sum_congr rfl
      intro ab hab
      exact hpoint ab
    _ = ∑ m ∈ K, ∑ n ∈ K, ∑ ab : X × X,
      (alpha m * χ (m : ZMod q)) *
        star (alpha n * χ (n : ZMod q)) *
        (H ab.1 ab.2 * star (F m ab.1) * G n ab.2) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.mul_sum]

/-- The SAME α(m)·χ(m) × conj(α(n)·χ(n)) factor, now inside the
LITERAL original C191 ν-dependent physical harmonic pairing. BIG source/
target marked prime tuples, full two-global Knu−RAW Fourier residual,
source measures, and real ζ/θ phase parameters remain unchanged.

This proves the exact cofactor-Fourier superposition interface; identifying
its `F m` and `G n` with the actual native Q/P PrimeSlotCore amplitudes
requires a separate, still-unproved physical/tag disintegration theorem. -/
theorem source_original_B435_true_physical_cofactor_character_superposition434
    {ι BG : Type} [Fintype ι] [DecidableEq ι]
       [Fintype BG] [DecidableEq BG]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (d : SourceComparisonData434 ι BG cfg x L Y Hprime)
    (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ)
    (hA hB : SourceOriginalProbePattern434 BG m → ℝ)
    (xi ζ theta : ℝ) (k : ℤ)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (χ : DirichletCharacter ℂ k.natAbs)
    (F G : (n : ℕ) → (ν : SourceOriginalProbePattern434 BG m) →
       SourceOriginalVariableBIGState434
         (fun g : BG => {p : ℕ // p ∈ d.Tb g})
         (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ)
    (ν : SourceOriginalProbePattern434 BG m) :
    sourceOriginalTrueNuSignedFullPhysicalPairing434 d J ell m hmJ
      Q hA hB xi ζ theta k
      (fun η a => ∑ n ∈ K,
        star (alpha n * χ (n : ZMod k.natAbs)) * F n η a)
      (fun η b => ∑ n ∈ K,
        star (alpha n * χ (n : ZMod k.natAbs)) * G n η b) ν =
    ∑ n ∈ K, ∑ n' ∈ K,
      (alpha n * χ (n : ZMod k.natAbs)) *
        star (alpha n' * χ (n' : ZMod k.natAbs)) *
        sourceOriginalTrueNuSignedFullPhysicalPairing434 d J ell m hmJ
          Q hA hB xi ζ theta k (F n) (G n') ν := by
  let BP : BG → Type := fun g => {p : ℕ // p ∈ d.Tb g}
  let free := sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν
  let mu := sourceOriginalJointHarmonicMu434 BP (fun _ p => p.val) d.Vbig
  let X := SourceOriginalVariableBIGState434 BP free
  let w := sourceOriginalVariableBIGMass434 BP free mu
  let error : X × X → ℂ := fun ab =>
    sourceOriginalProbeSignedMajorFourierError434
      J ell m hmJ ν d.Tb d.Vbig Q (hA ν) (hB ν) xi ζ theta k
      (fun g i => (ab.1 g i).val)
      (fun g i => (ab.2 g i).val)
  let H : X → X → ℂ := fun a b => ((w a*w b:ℝ):ℂ)*error (a,b)
  have hLeft :
      sourceOriginalTrueNuSignedFullPhysicalPairing434 d J ell m hmJ
        Q hA hB xi ζ theta k
        (fun η a => ∑ n ∈ K,
          star (alpha n * χ (n : ZMod k.natAbs)) * F n η a)
        (fun η b => ∑ n ∈ K,
          star (alpha n * χ (n : ZMod k.natAbs)) * G n η b) ν =
      ∑ ab : X × X,
        H ab.1 ab.2 *
          star (∑ n ∈ K,
            star (alpha n * χ (n : ZMod k.natAbs)) * F n ν ab.1) *
          (∑ n ∈ K,
            star (alpha n * χ (n : ZMod k.natAbs)) * G n ν ab.2) := by
    unfold sourceOriginalTrueNuSignedFullPhysicalPairing434
    apply Finset.sum_congr rfl
    intro ab hab
    dsimp only [H,error]
    ring
  have hTensor := source_original_B435_true_cofactor_character_bilinear434
    K alpha k.natAbs χ H (fun n a => F n ν a) (fun n b => G n ν b)
  calc
    _ = ∑ ab : X × X,
        H ab.1 ab.2 *
          star (∑ n ∈ K,
            star (alpha n * χ (n : ZMod k.natAbs)) * F n ν ab.1) *
          (∑ n ∈ K,
            star (alpha n * χ (n : ZMod k.natAbs)) * G n ν ab.2) := hLeft
    _ = ∑ n ∈ K, ∑ n' ∈ K,
        (alpha n * χ (n : ZMod k.natAbs)) *
          star (alpha n' * χ (n' : ZMod k.natAbs)) *
          (∑ ab : X × X,
             H ab.1 ab.2 * star (F n ν ab.1) * G n' ν ab.2) := hTensor
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro n' hn'
      congr 1
      unfold sourceOriginalTrueNuSignedFullPhysicalPairing434
      apply Finset.sum_congr rfl
      intro ab hab
      dsimp only [H,error]
      ring
end Green64Analytic.CorrelationSquare

end

end

/-! ## OriginalCofactorRawSignedProjection -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- True cofactor-resolved χ-test on the original ν-dependent free BIG
harmonic prime states. The cofactor twist χ(m) occurs BEFORE pairing,
independently of the BIG free-prime product. -/
noncomputable def sourceOriginalB436CofactorTest434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (d : SourceComparisonData434 ι G cfg x L Y Hprime)
    (J ell m : ℕ) (hmJ : m ≤ J) (K : Finset ℕ) (alpha : ℕ → ℂ)
    (k : ℤ) (χ : DirichletCharacter ℂ k.natAbs)
    (F : (n : ℕ) → (ν : SourceOriginalProbePattern434 G m) →
      SourceOriginalVariableBIGState434
        (fun g : G => {p : ℕ // p ∈ d.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ)
    (ν : SourceOriginalProbePattern434 G m)
    (a : SourceOriginalVariableBIGState434
        (fun g : G => {p : ℕ // p ∈ d.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν)) : ℂ :=
  ∑ n ∈ K, star (alpha n * χ (n : ZMod k.natAbs)) * F n ν a

/-- Literal source two-block sign from independently chosen two endpoint
projectors, before any normalization/square. -/
noncomputable def sourceOriginalB436TwoSign434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (tw : Bool × Bool) (ν : SourceOriginalProbePattern434 G m) : ℂ :=
  let shared := ((Fintype.card ι)*J) +
    ∑ g : G, (sourceOriginalProbeSharedSlots434 J ell m hmJ ν g).card
  (if tw.1 then (-1:ℂ)^shared else 1) *
    (if tw.2 then (-1:ℂ)^shared else 1)

/-- Three EXACT original source C191 ν-pairings; the selected branch
never changes their underlying harmonic law or ζ/θ physical phases.
0=RAW, 1=primitive Knu, 2=full signed primitive-minus-RAW residual. -/
noncomputable def sourceOriginalB436ThreePairings434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (d : SourceComparisonData434 ι G cfg x L Y Hprime)
    (blockA blockB : Finset G)
    (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ)
    (hA hB : SourceOriginalProbePattern434 G m → ℝ)
    (xi ζ theta : ℝ) (k : ℤ)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (F Gt : (n : ℕ) → (ν : SourceOriginalProbePattern434 G m) →
      SourceOriginalVariableBIGState434
        (fun g : G => {p : ℕ // p ∈ d.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ)
    (χ : DirichletCharacter ℂ k.natAbs) (tw : Bool × Bool)
    (kind : Fin 3) : ℂ :=
  let src := sourceOriginalB436CofactorTest434 d J ell m hmJ K alpha k χ F
  let tgt := sourceOriginalB436CofactorTest434 d J ell m hmJ K alpha k χ Gt
  ∑ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
    sourceOriginalB436TwoSign434 (ι := ι) J ell m hmJ tw ν *
    (if kind = 0 then
      sourceOriginalTrueNuPhysicalRawPairing434 d J ell m hmJ Q hA hB
        xi ζ theta k src tgt ν
     else if kind = 1 then
      sourceOriginalTrueNuPhysicalPrimitivePairing434 d J ell m hmJ Q hA hB
        xi ζ theta k src tgt ν
     else
      sourceOriginalTrueNuSignedFullPhysicalPairing434 d J ell m hmJ Q hA hB
        xi ζ theta k src tgt ν)

/-- Source RAW = primitive − signed for the literal **cofactor-χ twisted**
full two-block ν-family with a chosen original physical endpoint-sign pair.
RAW appears exactly once; no primitive conductor/cardinality multiplication.
The input is the genuine B380 physical identity, not a surrogate equality. -/
theorem source_original_B436_true_two_block_cofactor_raw_minus_signed434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (d : SourceComparisonData434 ι G cfg x L Y Hprime)
    (blockA blockB : Finset G)
    (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ)
    (hA hB : SourceOriginalProbePattern434 G m → ℝ)
    (xi ζ theta : ℝ) (k : ℤ)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (F Gt : (n : ℕ) → (ν : SourceOriginalProbePattern434 G m) →
      SourceOriginalVariableBIGState434
        (fun g : G => {p : ℕ // p ∈ d.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ)
    (χ : DirichletCharacter ℂ k.natAbs) (tw : Bool × Bool) :
    sourceOriginalB436ThreePairings434 d blockA blockB J ell m hmJ Q
      hA hB xi ζ theta k K alpha F Gt χ tw 0 =
    sourceOriginalB436ThreePairings434 d blockA blockB J ell m hmJ Q
      hA hB xi ζ theta k K alpha F Gt χ tw 1 -
    sourceOriginalB436ThreePairings434 d blockA blockB J ell m hmJ Q
      hA hB xi ζ theta k K alpha F Gt χ tw 2 := by
  classical
  let src := sourceOriginalB436CofactorTest434 d J ell m hmJ K alpha k χ F
  let tgt := sourceOriginalB436CofactorTest434 d J ell m hmJ K alpha k χ Gt
  dsimp only [sourceOriginalB436ThreePairings434]
  simp only [show (0 : Fin 3) = 0 by decide, show (1 : Fin 3) ≠ 0 by decide,
    show (1 : Fin 3) = 1 by decide, show (2 : Fin 3) ≠ 0 by decide,
    show (2 : Fin 3) ≠ 1 by decide, ite_true, ite_false]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro ν hν
  have h := source_original_true_nu_physical_RAW_eq_primitive_MINUS_signed434
    d J ell m hmJ Q hA hB xi ζ theta k src tgt ν
  rw [h]
  ring

/-- ORIGINAL physical C191 ν-family coefficient with the COMPLETE native
four-sign projector evaluated BEFORE norm square and character summation. -/
noncomputable def sourceOriginalB436ProjectedCoefficient434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (d : SourceComparisonData434 ι G cfg x L Y Hprime)
    (blockA blockB : Finset G)
    (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ)
    (hA hB : SourceOriginalProbePattern434 G m → ℝ)
    (xi ζ theta : ℝ) (k : ℤ)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (F Gt : (n : ℕ) → (ν : SourceOriginalProbePattern434 G m) →
      SourceOriginalVariableBIGState434
        (fun g : G => {p : ℕ // p ∈ d.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ)
    (χ : DirichletCharacter ℂ k.natAbs) (kind : Fin 3) : ℂ :=
  ∑ tw : Bool × Bool, sourceOriginalB430ParityCoefficient tw *
    sourceOriginalB436ThreePairings434 d blockA blockB J ell m hmJ Q
      hA hB xi ζ theta k K alpha F Gt χ tw kind

/-- Exact physical RAW-once decomposition AFTER the four-sign source
projector, for each character of the TRUE cofactor alpha expansion. -/
theorem source_original_B436_full_cofactor_four_sign_RAW_minus_signed434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (d : SourceComparisonData434 ι G cfg x L Y Hprime)
    (blockA blockB : Finset G)
    (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ)
    (hA hB : SourceOriginalProbePattern434 G m → ℝ)
    (xi ζ theta : ℝ) (k : ℤ)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (F Gt : (n : ℕ) → (ν : SourceOriginalProbePattern434 G m) →
      SourceOriginalVariableBIGState434
        (fun g : G => {p : ℕ // p ∈ d.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ)
    (χ : DirichletCharacter ℂ k.natAbs) :
    sourceOriginalB436ProjectedCoefficient434 d blockA blockB J ell m hmJ Q
      hA hB xi ζ theta k K alpha F Gt χ 0 =
    sourceOriginalB436ProjectedCoefficient434 d blockA blockB J ell m hmJ Q
      hA hB xi ζ theta k K alpha F Gt χ 1 -
    sourceOriginalB436ProjectedCoefficient434 d blockA blockB J ell m hmJ Q
      hA hB xi ζ theta k K alpha F Gt χ 2 := by
  unfold sourceOriginalB436ProjectedCoefficient434
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro tw htw
  rw [source_original_B436_true_two_block_cofactor_raw_minus_signed434
    d blockA blockB J ell m hmJ Q hA hB xi ζ theta k K alpha F Gt χ tw]
  ring

/-- The exact ORIGINAL source family Fourier-cofactor-χ four-sign RAW
mean-square is bounded by primitive and signed comparison mean-squares,
with coefficient two and no loss depending on |k|, ν, or four-sign channels.
This is a genuine consequence of the original physical RAW-once equality;
it does NOT assert either RHS is small without arithmetic input. -/
theorem source_original_B436_true_cofactor_projected_RAW_RMS_budget434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (d : SourceComparisonData434 ι G cfg x L Y Hprime)
    (blockA blockB : Finset G)
    (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ)
    (hA hB : SourceOriginalProbePattern434 G m → ℝ)
    (xi ζ theta : ℝ) (k : ℤ)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (F Gt : (n : ℕ) → (ν : SourceOriginalProbePattern434 G m) →
      SourceOriginalVariableBIGState434
        (fun g : G => {p : ℕ // p ∈ d.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ)
    (χ : DirichletCharacter ℂ k.natAbs) :
    (∑ χ : DirichletCharacter ℂ k.natAbs,
      ‖((k.natAbs.totient:ℂ)⁻¹)‖ *
        ‖sourceOriginalB436ProjectedCoefficient434 d blockA blockB J ell m hmJ Q
          hA hB xi ζ theta k K alpha F Gt χ 0‖^2) ≤
    (∑ χ : DirichletCharacter ℂ k.natAbs,
      ‖((k.natAbs.totient:ℂ)⁻¹)‖ *
        (2 * ‖sourceOriginalB436ProjectedCoefficient434
          d blockA blockB J ell m hmJ Q
          hA hB xi ζ theta k K alpha F Gt χ 1‖^2 +
         2 * ‖sourceOriginalB436ProjectedCoefficient434
          d blockA blockB J ell m hmJ Q
          hA hB xi ζ theta k K alpha F Gt χ 2‖^2)) := by
  apply Finset.sum_le_sum
  intro χ hχ
  let R := sourceOriginalB436ProjectedCoefficient434 d blockA blockB J ell m hmJ Q
    hA hB xi ζ theta k K alpha F Gt χ 0
  let P := sourceOriginalB436ProjectedCoefficient434 d blockA blockB J ell m hmJ Q
    hA hB xi ζ theta k K alpha F Gt χ 1
  let S := sourceOriginalB436ProjectedCoefficient434 d blockA blockB J ell m hmJ Q
    hA hB xi ζ theta k K alpha F Gt χ 2
  have hid : R = P - S := source_original_B436_full_cofactor_four_sign_RAW_minus_signed434
    d blockA blockB J ell m hmJ Q hA hB xi ζ theta k K alpha F Gt χ
  have hnorm : ‖R‖ ≤ ‖P‖ + ‖S‖ := by
    rw [hid]
    exact norm_sub_le P S
  have hsq : ‖R‖^2 ≤ (‖P‖ + ‖S‖)^2 :=
    pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  have htwo : ‖R‖^2 ≤ 2*‖P‖^2 + 2*‖S‖^2 := by
    nlinarith only [hsq, sq_nonneg (‖P‖ - ‖S‖)]
  exact mul_le_mul_of_nonneg_left htwo (norm_nonneg _)
end Green64Analytic.CorrelationSquare

end

end

