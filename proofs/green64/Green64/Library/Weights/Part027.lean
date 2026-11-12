module

public import Green64.Library.Weights.GhostReturnLiteralRow
public import Green64.Library.Weights.Part018
public import Green64.Library.Correlation.Part028
public import Green64.Library.Correlation.Part029
public import Green64.Library.Correlation.PhysicalENeverActive

@[expose] public section

/-!
# Weights / Part027

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalGhostReturnBirthGate -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- For one numerical prime the original GLOBAL birth rule forces
b<=1, and forbids any second birth after that prime has been seen.
There is no coordinatewise substitute for numerical distinctness. -/
theorem source_original_GHOST_RETURN_single_prime_birth_gate434
    (p : ℕ) (seen : Finset ℕ) (b : ℕ) :
    (List.replicate b p).Nodup ∧ Disjoint seen (List.replicate b p).toFinset ↔
      b ≤ 1 ∧ (b=0 ∨ p ∉ seen) := by
  cases b with
  | zero => simp
  | succ b =>
    cases b with
    | zero => simp
    | succ b => simp [List.replicate_succ]

/-- The actual birth gate, rather than an analytic cutoff assumption,
removes every b>=2 term. This works with the original arbitrary
Fock/birth cutoff B>=1 and arbitrary complex witness weights. -/
theorem source_original_GHOST_RETURN_birth_cutoff_exact434
    (p : ℕ) (seen : Finset ℕ) (B : ℕ) (hB : 1 ≤ B) (f : ℕ → ℂ) :
    (∑ b ∈ Finset.range (B+1),
      if (List.replicate b p).Nodup ∧
          Disjoint seen (List.replicate b p).toFinset then f b else 0) =
    ∑ b ∈ Finset.range 2,
      if b=0 ∨ p ∉ seen then f b else 0 := by
  have hs : Finset.range 2 ⊆ Finset.range (B+1) := Finset.range_mono (by omega)
  calc
    _ = ∑ b ∈ Finset.range 2,
        if (List.replicate b p).Nodup ∧
          Disjoint seen (List.replicate b p).toFinset then f b else 0 := by
      symm
      apply Finset.sum_subset hs
      intro b hb hnot
      apply if_neg
      intro hg
      have hsmall := (source_original_GHOST_RETURN_single_prime_birth_gate434 p seen b).mp hg
      have hnot' : ¬b<2 := by simpa only [Finset.mem_range] using hnot
      omega
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b hb
      have hb' : b ≤ 1 := by have := Finset.mem_range.mp hb;omega
      simp only [source_original_GHOST_RETURN_single_prime_birth_gate434,
        hb',true_and]

def sourceOriginalGhostReturnMapState434 {R S : Type} (e : R ≃ S) :
    SourceOriginalGhostReturnState434 R → SourceOriginalGhostReturnState434 S
  | .unborn => .unborn
  | .pending r => .pending (e r)
  | .retired => .retired

/-- Residue re-anchoring is a true equivalence of the literal ghost
row, including both seen histories and all signed coefficients. -/
theorem source_original_GHOST_RETURN_literal_equiv434
    {R S : Type} [Fintype R] [Fintype S] [DecidableEq R] [DecidableEq S]
    (e : R ≃ S) (a : R) (eta lambda : ℝ)
    (s : SourceOriginalGhostReturnState434 R)
    (F : SourceOriginalGhostReturnState434 S → ℂ) :
    sourceOriginalGhostReturnLiteralRow434 a eta lambda s
        (fun x => F (sourceOriginalGhostReturnMapState434 e x)) =
    sourceOriginalGhostReturnLiteralRow434 (e a) eta lambda
        (sourceOriginalGhostReturnMapState434 e s) F := by
  cases s with
  | unborn =>
    simp only [source_original_GHOST_RETURN_literal_unborn434,
      sourceOriginalGhostReturnMapState434]
  | retired =>
    simp only [source_original_GHOST_RETURN_literal_retired434,
      sourceOriginalGhostReturnMapState434]
  | pending r =>
    simp only [source_original_GHOST_RETURN_literal_pending434,
      sourceOriginalGhostReturnMapState434]
    by_cases h : r=a
    · simp [h]
    · have he : e r ≠ e a := fun hh => h (e.injective hh)
      simp [h,he]

def sourceOriginalGhostReturnTranslate434 {p : ℕ} (a : ZMod p) : ZMod p ≃ ZMod p where
  toFun r := r-a
  invFun r := r+a
  left_inv r := by simp
  right_inv r := by simp

/-- The arbitrary return class a is the original zero-residue G row
in the actual translated coordinate r-a. Exact returns are retained. -/
theorem source_original_GHOST_RETURN_literal_zero_coordinate434
    {p : ℕ} [NeZero p] (a : ZMod p) (eta lambda : ℝ)
    (s : SourceOriginalGhostReturnState434 (ZMod p))
    (F : SourceOriginalGhostReturnState434 (ZMod p) → ℂ) :
    sourceOriginalGhostReturnLiteralRow434 a eta lambda s
        (fun x => F (sourceOriginalGhostReturnMapState434
          (sourceOriginalGhostReturnTranslate434 a) x)) =
    sourceOriginalGhostReturnLiteralRow434 (0:ZMod p) eta lambda
        (sourceOriginalGhostReturnMapState434 (sourceOriginalGhostReturnTranslate434 a) s) F := by
  have h := source_original_GHOST_RETURN_literal_equiv434
    (sourceOriginalGhostReturnTranslate434 a) a eta lambda s F
  simpa only [sourceOriginalGhostReturnTranslate434,Equiv.coe_fn_mk,sub_self] using h
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalGhostReturnMarkedVacuum -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 14000000

def sourceOriginalGhostReturnLiteralChain434 {R : Type} [Fintype R] [DecidableEq R]
    (visits : List (R × ℝ)) (lambda : ℝ)
    (F : SourceOriginalGhostReturnState434 R → ℂ) :
    SourceOriginalGhostReturnState434 R → ℂ :=
  match visits with
  | [] => F
  | v::vs => fun s => sourceOriginalGhostReturnLiteralRow434 v.1 v.2 lambda s
      (sourceOriginalGhostReturnLiteralChain434 vs lambda F)

/-- Arbitrary complex observations of the two vacuum histories.
No identification of birth parity with arithmetic parity is used. -/
def sourceOriginalGhostReturnTerminal434 {R : Type} (A B : ℂ) :
    SourceOriginalGhostReturnState434 R → ℂ
  | .unborn => A
  | .pending _ => 0
  | .retired => B

theorem source_original_GHOST_RETURN_literal_chain_terminal434
    {R : Type} [Fintype R] [DecidableEq R]
    (visits : List (R × ℝ)) (lambda : ℝ) (A B : ℂ) :
    sourceOriginalGhostReturnLiteralChain434 visits lambda
        (sourceOriginalGhostReturnTerminal434 A B) .retired = B ∧
    (∀ r, sourceOriginalGhostReturnLiteralChain434 visits lambda
        (sourceOriginalGhostReturnTerminal434 A B) (.pending r) =
      -((1-sourceOriginalGhostReturnSurvival434 visits r:ℝ):ℂ)*B) ∧
    sourceOriginalGhostReturnLiteralChain434 visits lambda
        (sourceOriginalGhostReturnTerminal434 A B) .unborn =
      A+(lambda:ℂ)*(sourceOriginalGhostReturnLoops434 visits:ℂ)*B := by
  induction visits with
  | nil => simp [sourceOriginalGhostReturnLiteralChain434,
      sourceOriginalGhostReturnTerminal434,sourceOriginalGhostReturnSurvival434,
      sourceOriginalGhostReturnLoops434]
  | cons v vs ih =>
    rcases v with ⟨a,eta⟩
    refine ⟨?_,?_,?_⟩
    · simpa only [sourceOriginalGhostReturnLiteralChain434,
        source_original_GHOST_RETURN_literal_retired434] using ih.1
    · intro r
      simp only [sourceOriginalGhostReturnLiteralChain434,
        source_original_GHOST_RETURN_literal_pending434,
        sourceOriginalGhostReturnSurvival434]
      rw [ih.1,ih.2.1 r]
      split_ifs <;> push_cast <;> ring
    · simp only [sourceOriginalGhostReturnLiteralChain434,
        source_original_GHOST_RETURN_literal_unborn434,sourceOriginalGhostReturnLoops434]
      rw [ih.2.2,ih.2.1 a]
      push_cast
      ring

theorem source_original_GHOST_RETURN_loops_nonneg434
    {R : Type} [DecidableEq R] (visits : List (R × ℝ))
    (heta : ∀ v ∈ visits,0 ≤ v.2 ∧ v.2 ≤ 1) :
    0 ≤ sourceOriginalGhostReturnLoops434 visits := by
  induction visits with
  | nil => exact le_rfl
  | cons v vs ih =>
    have hv := heta v List.mem_cons_self
    have ht := fun w hw => heta w (List.mem_cons_of_mem v hw)
    exact add_nonneg (mul_nonneg hv.1
      (sub_nonneg.mpr (source_original_GHOST_RETURN_survival_unit434 vs ht v.1).2))
      (ih ht)

/-- A genuine complex marked vacuum pairing, not a per-row oscillatory
saving: baseline times the complete once-born sourceGhostTerm chain is
bounded by the common envelope of BOTH terminal histories. -/
theorem source_original_GHOST_RETURN_BASELINE_terminal_envelope434
    {R : Type} [Fintype R] [DecidableEq R] [Nonempty R]
    (visits : List (R × ℝ))
    (heta : ∀ v ∈ visits,0 ≤ v.2 ∧ v.2 ≤ 1)
    (hb : 0 < 1-(visits.map Prod.snd).sum/(Fintype.card R:ℝ))
    (A B : ℂ) (M : ℝ) (hA : ‖A‖ ≤ M) (hB : ‖B‖ ≤ M) :
    let p : ℝ := Fintype.card R
    let b := 1-(visits.map Prod.snd).sum/p
    ‖(b:ℂ)*sourceOriginalGhostReturnLiteralChain434 visits (1/(p*b))
      (sourceOriginalGhostReturnTerminal434 A B) .unborn‖ ≤ M := by
  let p : ℝ := Fintype.card R
  let b := 1-(visits.map Prod.snd).sum/p
  let lam := 1/(p*b)
  let c := b*lam*sourceOriginalGhostReturnLoops434 visits
  have hp : 0 < p := by dsimp [p];exact_mod_cast Fintype.card_pos
  have hb' : 0 < b := hb
  have hl : 0 ≤ lam := by dsimp [lam];positivity
  have hc : 0 ≤ c := mul_nonneg (mul_nonneg hb'.le hl)
    (source_original_GHOST_RETURN_loops_nonneg434 visits heta)
  have hM : 0 ≤ M := (norm_nonneg A).trans hA
  have hu := (source_original_GHOST_RETURN_BASELINE_unit434 visits heta (ne_of_gt hb)).2
  rw [(source_original_GHOST_RETURN_chain_exact434 visits _).2.2] at hu
  have hbc : b+c ≤ 1 := by
    change b*(1+lam*sourceOriginalGhostReturnLoops434 visits) ≤ 1 at hu
    dsimp only [c]
    nlinarith only [hu]
  change ‖(b:ℂ)*sourceOriginalGhostReturnLiteralChain434 visits lam
    (sourceOriginalGhostReturnTerminal434 A B) .unborn‖ ≤ M
  rw [(source_original_GHOST_RETURN_literal_chain_terminal434 visits lam A B).2.2]
  have heq : (b:ℂ)*(A+(lam:ℂ)*(sourceOriginalGhostReturnLoops434 visits:ℂ)*B) =
      (b:ℂ)*A+(c:ℂ)*B := by
    dsimp [c]
    push_cast
    ring
  rw [heq]
  calc
    _ ≤ ‖(b:ℂ)*A‖+‖(c:ℂ)*B‖ := norm_add_le _ _
    _ = b*‖A‖+c*‖B‖ := by
      simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg hb'.le,abs_of_nonneg hc]
    _ ≤ b*M+c*M := add_le_add (mul_le_mul_of_nonneg_left hA hb'.le)
      (mul_le_mul_of_nonneg_left hB hc)
    _ = (b+c)*M := by ring
    _ ≤ M := by nlinarith only [hbc,hM]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSourceEReindex -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 18000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (M : ℕ) (cap : BG → ℕ)

def sourceOriginalFullEReindexState434
    (x : FullPhysicalState SP sm BP bm M cap)
    (e : (g : BG) → Equiv.Perm (Fin (x.2 g).2.1.val)) :
    FullPhysicalState SP sm BP bm M cap :=
  (x.1,fun g => sourceOriginalEReindexState434 (bm g) M (cap g) (x.2 g) (e g))

def sourceOriginalFullEBranchReindex434
    (x : FullPhysicalState SP sm BP bm M cap)
    (e : (g : BG) → Equiv.Perm (Fin (x.2 g).2.1.val)) :
    FullPhysicalEdgeBranch SP sm BP bm M cap x ≃
      FullPhysicalEdgeBranch SP sm BP bm M cap
        (sourceOriginalFullEReindexState434 SP sm BP bm M cap x e) where
  toFun b := {
    sigmaBig := b.sigmaBig
    tauBig := b.tauBig
    bigChoice := fun g => ((b.bigChoice g).1,
      sourceOriginalEChoiceReindex434 (bm g) M (cap g) (x.2 g) (e g) (b.bigChoice g).2)
    smallTarget := b.smallTarget }
  invFun b := {
    sigmaBig := b.sigmaBig
    tauBig := b.tauBig
    bigChoice := fun g => ((b.bigChoice g).1,
      (sourceOriginalEChoiceReindex434 (bm g) M (cap g) (x.2 g) (e g)).symm (b.bigChoice g).2)
    smallTarget := b.smallTarget }
  left_inv := by
    intro b
    cases b with
    | mk s t c u =>
      dsimp only
      congr 1
      funext g
      exact Prod.ext rfl (Equiv.symm_apply_apply _ _)
  right_inv := by
    intro b
    cases b with
    | mk s t c u =>
      dsimp only
      congr 1
      funext g
      exact Prod.ext rfl (Equiv.apply_symm_apply _ _)

theorem source_original_FULL_E_reindex_projection434
    (x : FullPhysicalState SP sm BP bm M cap)
    (e : (g : BG) → Equiv.Perm (Fin (x.2 g).2.1.val)) :
    physicalFockProjection SP sm BP bm M cap
      (sourceOriginalFullEReindexState434 SP sm BP bm M cap x e) =
    physicalFockProjection SP sm BP bm M cap x := by
  apply Prod.ext
  · rfl
  · funext g
    exact Prod.ext rfl (source_original_E_reindex_fock434 (bm g) M (cap g) (x.2 g) (e g))

variable (J ell m : ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

def sourceOriginalFullEChoiceReindex434
    (x : FullPhysicalState SP sm BP bm (J+ell) cap)
    (e : (g : BG) → Equiv.Perm (Fin (x.2 g).2.1.val)) :
    FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x ≃
    FullOrientedSourceChoice SP sm BP bm J ell m cap patterns
      (sourceOriginalFullEReindexState434 SP sm BP bm (J+ell) cap x e) :=
  Equiv.sigmaCongrRight (fun _ => Equiv.prodCongr (Equiv.refl _)
    (Equiv.prodCongr (sourceOriginalFullEBranchReindex434 SP sm BP bm (J+ell) cap x e)
      (Equiv.refl _)))

theorem source_original_SOURCE_E_reindex_legal434
    (x : FullPhysicalState SP sm BP bm (J+ell) cap)
    (e : (g : BG) → Equiv.Perm (Fin (x.2 g).2.1.val)) (o k : ℤ)
    (z : FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x) :
    sourceOrientedPhysicalLegal SP sm BP bm J ell m cap patterns
      (sourceOriginalFullEReindexState434 SP sm BP bm (J+ell) cap x e) o k
      (sourceOriginalFullEChoiceReindex434 SP sm BP bm cap J ell m patterns x e z) ↔
    sourceOrientedPhysicalLegal SP sm BP bm J ell m cap patterns x o k z := by
  constructor
  · intro hz
    refine ⟨hz.1,hz.2.1,hz.2.2.1,?_,hz.2.2.2.2⟩
    intro g
    exact (source_original_E_reindex_legal434 (bm g) (J+ell) (cap g)
      (x.2 g) (e g) (z.2.2.1.bigChoice g).1
      (sourceBigShared J ell m (patterns z.1) g)
      (z.2.2.1.sigmaBig g) (z.2.2.1.tauBig g)
      (sourceOrientedPhysicalD SP sm BP bm J ell m cap
        (patterns z.1) z.2.1 x z.2.2.1.sigmaBig z.2.2.2.1)
      (sourceOrientedStep SP sm BP bm J ell m cap
        (patterns z.1) z.2.1 x z.2.2.1.sigmaBig z.2.2.2.1 o k)
      (z.2.2.1.bigChoice g).2).mp (hz.2.2.2.1 g)
  · intro hz
    refine ⟨hz.1,hz.2.1,hz.2.2.1,?_,hz.2.2.2.2⟩
    intro g
    exact (source_original_E_reindex_legal434 (bm g) (J+ell) (cap g)
      (x.2 g) (e g) (z.2.2.1.bigChoice g).1
      (sourceBigShared J ell m (patterns z.1) g)
      (z.2.2.1.sigmaBig g) (z.2.2.1.tauBig g)
      (sourceOrientedPhysicalD SP sm BP bm J ell m cap
        (patterns z.1) z.2.1 x z.2.2.1.sigmaBig z.2.2.2.1)
      (sourceOrientedStep SP sm BP bm J ell m cap
        (patterns z.1) z.2.1 x z.2.2.1.sigmaBig z.2.2.2.1 o k)
      (z.2.2.1.bigChoice g).2).mpr (hz.2.2.2.1 g)

theorem source_original_SOURCE_E_reindex_output434
    (x : FullPhysicalState SP sm BP bm (J+ell) cap)
    (e : (g : BG) → Equiv.Perm (Fin (x.2 g).2.1.val)) (o k : ℤ)
    (z : FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x) :
    sourceOrientedPhysicalOutput SP sm BP bm J ell m cap patterns
      (sourceOriginalFullEReindexState434 SP sm BP bm (J+ell) cap x e) o k
      (sourceOriginalFullEChoiceReindex434 SP sm BP bm cap J ell m patterns x e z) =
    sourceOrientedPhysicalOutput SP sm BP bm J ell m cap patterns x o k z := by
  apply Prod.ext
  · rfl
  · funext g
    apply Prod.ext
    · rfl
    · exact source_original_E_reindex_pending434 (bm g) (J+ell) (cap g) (x.2 g) (e g)
        (z.2.2.1.sigmaBig g)
        (sourceOrientedStep SP sm BP bm J ell m cap (patterns z.1) z.2.1
          x z.2.2.1.sigmaBig z.2.2.2.1 o k) (z.2.2.1.bigChoice g).2

theorem source_original_SOURCE_E_reindex_births434
    (x : FullPhysicalState SP sm BP bm (J+ell) cap)
    (e : (g : BG) → Equiv.Perm (Fin (x.2 g).2.1.val))
    (z : FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x) :
    orientedEFreshBirths SP sm BP bm J ell m cap patterns
      (sourceOriginalFullEChoiceReindex434 SP sm BP bm cap J ell m patterns x e z) =
    orientedEFreshBirths SP sm BP bm J ell m cap patterns z := rfl

theorem source_original_SOURCE_E_reindex_coefficient434
    (x : FullPhysicalState SP sm BP bm (J+ell) cap)
    (e : (g : BG) → Equiv.Perm (Fin (x.2 g).2.1.val))
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (z : FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x) :
    sourceOrientedPhysicalCoefficient SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta o k
      (sourceOriginalFullEReindexState434 SP sm BP bm (J+ell) cap x e)
      (sourceOriginalFullEChoiceReindex434 SP sm BP bm cap J ell m patterns x e z) =
    sourceOrientedPhysicalCoefficient SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta o k x z := by
  unfold sourceOrientedPhysicalCoefficient
  dsimp only
  congr 2
  apply Finset.prod_congr rfl
  intro g hg
  exact source_original_E_reindex_coefficient434 (bm g) (J+ell) (cap g)
    (x.2 g) (e g) (mu g) (V g) rho (z.2.2.1.bigChoice g).1
    (sourceBigShared J ell m (patterns z.1) g)
    (z.2.2.1.sigmaBig g) (z.2.2.1.tauBig g)
    (sourceOrientedStep SP sm BP bm J ell m cap
      (patterns z.1) z.2.1 x z.2.2.1.sigmaBig z.2.2.2.1 o k)
    (z.2.2.1.bigChoice g).2

/-- Exact OLD-order invariance of the entire original marked E row:
joint K, phases, all groups/patterns/auxiliaries/permutations, actual
fresh numerical gate and arbitrary joint terminal test are retained. -/
theorem source_original_SOURCE_MARKED_E_reindex434
    (x : FullPhysicalState SP sm BP bm (J+ell) cap)
    (e : (g : BG) → Equiv.Perm (Fin (x.2 g).2.1.val))
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (seen : Finset ℕ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ) :
    physicalOrientedBirthMarkedE SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta o k
      (sourceOriginalFullEReindexState434 SP sm BP bm (J+ell) cap x e) seen F =
    physicalOrientedBirthMarkedE SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta o k x seen F := by
  unfold physicalOrientedBirthMarkedE sourceOrientedPhysicalChoices
  simp only [Finset.sum_filter]
  symm
  apply Fintype.sum_equiv (sourceOriginalFullEChoiceReindex434
    SP sm BP bm cap J ell m patterns x e)
  intro z
  rw [source_original_SOURCE_E_reindex_legal434,
    source_original_SOURCE_E_reindex_coefficient434,
    source_original_SOURCE_E_reindex_output434]
  simp only [orientedEFreshBatchEligible,source_original_SOURCE_E_reindex_births434]
  rfl
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSourceEOrbit -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- Equal nodup Fock multisets have actual OLD-index representatives
related by a permutation. The ambient carrier is not restricted. -/
theorem source_original_FOCK_nodup_reindex434
    {U : Type} {B : ℕ} (s t : FockState U B)
    (hst : fockMultiset s=fockMultiset t) (hn : (fockMultiset t).Nodup) :
    ∃ e : Equiv.Perm (Fin s.1.val),
      (⟨s.1,fun j => s.2 (e j)⟩ : FockState U B)=t := by
  rcases s with ⟨sn,f⟩
  rcases t with ⟨tn,g⟩
  have hl : sn=tn := by
    apply Fin.ext
    have hh := congrArg Multiset.card hst
    simpa only [fockMultiset,Multiset.coe_card,List.length_ofFn] using hh
  subst tn
  have hg : Function.Injective g := by
    exact List.nodup_ofFn.mp hn
  have hex (j : Fin sn.val) : ∃ i,f i=g j := by
    have hm : g j ∈ fockMultiset (⟨sn,g⟩ : FockState U B) := by
      simp [fockMultiset]
    rw [←hst] at hm
    simpa only [fockMultiset,Multiset.mem_coe,List.mem_ofFn] using hm
  choose e he using hex
  have hi : Function.Injective e := by
    intro i j hij
    apply hg
    rw [←he i,←he j,hij]
  refine ⟨Equiv.ofBijective e ⟨hi,Finite.surjective_of_injective hi⟩,?_⟩
  congr 1
  funext j
  exact he j

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (M : ℕ) (cap : BG → ℕ)

theorem source_original_REACHABLE_orbit_reindex434
    (x y : FullPhysicalState SP sm BP bm M cap) (seen : Finset ℕ)
    (hxy : physicalFockProjection SP sm BP bm M cap x =
      physicalFockProjection SP sm BP bm M cap y)
    (hy : sourceOriginalPhysicalReachable434 SP sm BP bm M
      (physicalFockProjection SP sm BP bm M cap y) seen) :
    ∃ e : (g : BG) → Equiv.Perm (Fin (x.2 g).2.1.val),
      sourceOriginalFullEReindexState434 SP sm BP bm M cap x e = y := by
  have ho := (source_original_PHYSICAL_reachable_pending434 SP sm BP bm M cap y seen hy).1
  have he (g : BG) : ∃ e : Equiv.Perm (Fin (x.2 g).2.1.val),
      (⟨(x.2 g).2.1,fun j => (x.2 g).2.2 (e j)⟩ :
        FockState (Atom (BP g) (bm g)) (cap g)) = (y.2 g).2 := by
    apply source_original_FOCK_nodup_reindex434
    · exact congrArg (fun z : FullPhysicalOutput SP sm BP bm M => (z.2 g).2) hxy
    · exact (ho g).of_map (fun z => z.1)
  choose e he using he
  refine ⟨e,?_⟩
  apply Prod.ext
  · exact congrArg (fun z : FullPhysicalOutput SP sm BP bm M => z.1) hxy
  · funext g
    exact Prod.ext (congrArg (fun z : FullPhysicalOutput SP sm BP bm M => (z.2 g).1) hxy) (he g)

variable (J ell m : ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

theorem source_original_SOURCE_MARKED_E_orbit_invariant434
    (x y : FullPhysicalState SP sm BP bm (J+ell) cap) (seen : Finset ℕ)
    (hxy : physicalFockProjection SP sm BP bm (J+ell) cap x =
      physicalFockProjection SP sm BP bm (J+ell) cap y)
    (hy : sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell)
      (physicalFockProjection SP sm BP bm (J+ell) cap y) seen)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ) :
    physicalOrientedBirthMarkedE SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta o k y seen F =
    physicalOrientedBirthMarkedE SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta o k x seen F := by
  obtain ⟨e,rfl⟩ := source_original_REACHABLE_orbit_reindex434
    SP sm BP bm (J+ell) cap x y seen hxy hy
  exact source_original_SOURCE_MARKED_E_reindex434 SP sm BP bm cap J ell m patterns
    x e q rho Vs V mu K zeta theta o k seen F

/-- On the reachable sector, the original weighted symmetric E is exactly
the original E row of ANY physical OLD representative. The true Fock
orbit mass cancels once; no uniform counting measure or second factorial. -/
theorem source_original_SOURCE_SYMMETRIC_E_representative434
    (x : FullPhysicalState SP sm BP bm (J+ell) cap) (seen : Finset ℕ)
    (hx : sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell)
      (physicalFockProjection SP sm BP bm (J+ell) cap x) seen)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0 < Vs g) (hmu : ∀ g p,0 < mu g p)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ) :
    physicalOrientedMarkedSymmetricE SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta o k
      (physicalFockProjection SP sm BP bm (J+ell) cap x) seen F =
    physicalOrientedBirthMarkedE SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta o k x seen F := by
  let out := physicalFockProjection SP sm BP bm (J+ell) cap x
  have hpos : (physicalOrbitMass SP sm BP bm (J+ell) cap Vs mu out : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (physicalOrbitMass_pos SP sm BP bm (J+ell) cap
      Vs mu hVs hmu out (Finset.mem_image.mpr ⟨x,Finset.mem_univ x,rfl⟩)))
  have hc (y : FullPhysicalState SP sm BP bm (J+ell) cap)
      (hy : physicalFockProjection SP sm BP bm (J+ell) cap y=out) :
      physicalOrientedBirthMarkedE SP sm BP bm J ell m cap patterns
        q rho Vs V mu K zeta theta o k y seen F =
      physicalOrientedBirthMarkedE SP sm BP bm J ell m cap patterns
        q rho Vs V mu K zeta theta o k x seen F := by
    exact (source_original_SOURCE_MARKED_E_orbit_invariant434
      SP sm BP bm cap J ell m patterns y x seen hy hx
      q rho Vs V mu K zeta theta o k F).symm
  unfold physicalOrientedMarkedSymmetricE fullPhysicalOrbitAverage
  change (∑ y ∈ (Finset.univ : Finset (FullPhysicalState SP sm BP bm (J+ell) cap))
      with physicalFockProjection SP sm BP bm (J+ell) cap y=out,
      (fullPhysicalMass SP sm BP bm (J+ell) cap Vs mu y : ℂ) *
        physicalOrientedBirthMarkedE SP sm BP bm J ell m cap patterns
          q rho Vs V mu K zeta theta o k y seen F) /
      (physicalOrbitMass SP sm BP bm (J+ell) cap Vs mu out : ℂ) = _
  have hn :
      (∑ y ∈ (Finset.univ : Finset (FullPhysicalState SP sm BP bm (J+ell) cap))
        with physicalFockProjection SP sm BP bm (J+ell) cap y=out,
        (fullPhysicalMass SP sm BP bm (J+ell) cap Vs mu y : ℂ) *
          physicalOrientedBirthMarkedE SP sm BP bm J ell m cap patterns
            q rho Vs V mu K zeta theta o k y seen F) =
      (physicalOrbitMass SP sm BP bm (J+ell) cap Vs mu out : ℂ) *
        physicalOrientedBirthMarkedE SP sm BP bm J ell m cap patterns
          q rho Vs V mu K zeta theta o k x seen F := by
    unfold physicalOrbitMass
    push_cast
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro y hy
    rw [hc y (Finset.mem_filter.mp hy).2]
  rw [hn]
  exact mul_div_cancel_left₀ _ hpos
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalGhostSetReindex -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock Green64MemoryGhostOp
set_option autoImplicit false
set_option maxHeartbeats 18000000

theorem source_original_nodup_list_index_equiv434
    {U : Type} (a b : List U) (ha : a.Nodup) (hb : b.Nodup)
    (hab : (a : Multiset U)=(b : Multiset U)) :
    ∃ e : Fin b.length ≃ Fin a.length,∀ j,a.get (e j)=b.get j := by
  have hp := Multiset.coe_eq_coe.mp hab
  have hai : Function.Injective a.get := by
    apply List.nodup_ofFn.mp
    simpa only [List.ofFn_get] using ha
  have hbi : Function.Injective b.get := by
    apply List.nodup_ofFn.mp
    simpa only [List.ofFn_get] using hb
  have he (j : Fin b.length) : ∃ i,a.get i=b.get j :=
    List.mem_iff_get.mp (hp.mem_iff.mpr (List.get_mem b j))
  have hf (i : Fin a.length) : ∃ j,b.get j=a.get i :=
    List.mem_iff_get.mp (hp.mem_iff.mp (List.get_mem a i))
  choose e he using he
  choose f hf using hf
  refine ⟨⟨e,f,?_,?_⟩,he⟩
  · intro j
    apply hbi
    rw [hf,he]
  · intro i
    apply hai
    rw [he,hf]

variable {P : Type} [Fintype P] [DecidableEq P]
variable (a b : List P) (zero : P → Prop) [DecidablePred zero]
variable (e : Fin b.length ≃ Fin a.length)
variable (he : ∀ j,a.get (e j)=b.get j)

theorem source_original_G_reindex_mem434 (A : Finset (Fin a.length)) (j : Fin b.length) :
    j ∈ e.symm.finsetCongr A ↔ e j ∈ A := by
  change j ∈ A.map e.symm.toEmbedding ↔ e j ∈ A
  constructor
  · intro h
    obtain ⟨i,hi,hij⟩ := Finset.mem_map.mp h
    change e.symm i=j at hij
    have h' : i=e j := by
      simpa only [Equiv.apply_symm_apply] using congrArg e hij
    simpa only [←h'] using hi
  · intro h
    exact Finset.mem_map.mpr ⟨e j,h,e.symm_apply_apply j⟩

include he in
theorem source_original_G_reindex_zero_card434 :
    (zeroOld b zero).card=(zeroOld a zero).card := by
  unfold zeroOld
  rw [Finset.card_filter,Finset.card_filter]
  apply Fintype.sum_equiv e
  intro j
  rw [he]

def sourceOriginalGhostOldSetReindex434 :
    {A : Finset (Fin a.length) // A ∈ (zeroOld a zero).powerset} ≃
    {A : Finset (Fin b.length) // A ∈ (zeroOld b zero).powerset} :=
  Equiv.subtypeEquiv e.symm.finsetCongr (by
    intro A
    simp only [Finset.mem_powerset]
    constructor
    · intro h j hj
      have hj' := (source_original_G_reindex_mem434 a b e A j).mp hj
      have hz := (Finset.mem_filter.mp (h hj')).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      rwa [←he]
    · intro h i hi
      have hj := h ((source_original_G_reindex_mem434 a b e A (e.symm i)).mpr
        (by simpa only [Equiv.apply_symm_apply] using hi))
      have hz := (Finset.mem_filter.mp hj).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      rw [←he,Equiv.apply_symm_apply] at hz
      exact hz)

def sourceOriginalGhostSetReindex434 :
    SourceOriginalGhostSetChoice434 a zero ≃ SourceOriginalGhostSetChoice434 b zero :=
  Equiv.prodCongr (sourceOriginalGhostOldSetReindex434 a b zero e he) (Equiv.refl _)

theorem source_original_G_reindex_delete_card434
    (A : {A : Finset (Fin a.length) // A ∈ (zeroOld a zero).powerset}) :
    ((sourceOriginalGhostOldSetReindex434 a b zero e he A).1).card=A.1.card := by
  exact Finset.card_map e.symm.toEmbedding

include he in
theorem source_original_G_reindex_survivor_bag434
    (A : Finset (Fin a.length)) :
    memoryTupleBag (fun j : {j : Fin b.length // j ∉ e.symm.finsetCongr A} => b.get j) =
      memoryTupleBag (fun j : {j : Fin a.length // j ∉ A} => a.get j) := by
  let er : {j : Fin b.length // j ∉ e.symm.finsetCongr A} ≃
      {j : Fin a.length // j ∉ A} :=
    Equiv.subtypeEquiv e (fun j => not_congr (source_original_G_reindex_mem434 a b e A j))
  unfold memoryTupleBag
  apply Fintype.sum_equiv er
  intro j
  change ({b.get j.val} : Multiset P) = {a.get (e j.val)}
  rw [he]

theorem source_original_G_reindex_set_coefficient434
    (B : ℕ) (alpha chi gamma : ℂ) (nu : P → ℂ)
    (d : SourceOriginalGhostSetChoice434 a zero) :
    sourceOriginalGhostSetCoefficient434 b zero B alpha chi gamma nu
      (sourceOriginalGhostSetReindex434 a b zero e he d) =
    sourceOriginalGhostSetCoefficient434 a zero B alpha chi gamma nu d := by
  unfold sourceOriginalGhostSetCoefficient434
  change (if d.2.card ≤ B then
      alpha^((sourceOriginalGhostOldSetReindex434 a b zero e he d.1).1).card *
        chi^((zeroOld b zero).card-((sourceOriginalGhostOldSetReindex434 a b zero e he d.1).1).card) *
        gamma^d.2.card * (∏ p ∈ d.2,nu p) else 0) = _
  rw [source_original_G_reindex_delete_card434,source_original_G_reindex_zero_card434 a b zero e he]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalGhostAtomSubsets -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock Green64MemoryGhostOp
set_option autoImplicit false
set_option maxHeartbeats 18000000

def sourceOriginalSubsetEmbeddingEquiv434
    {I P : Type} [DecidableEq I] [DecidableEq P]
    (s : Finset I) (f : I ↪ P) :
    {A : Finset I // A ∈ s.powerset} ≃
      {B : Finset P // B ∈ (s.map f).powerset} where
  toFun A := ⟨A.1.map f,by
    apply Finset.mem_powerset.mpr
    intro p hp
    obtain ⟨i,hi,hip⟩ := Finset.mem_map.mp hp
    exact Finset.mem_map.mpr ⟨i,(Finset.mem_powerset.mp A.2) hi,hip⟩⟩
  invFun B := ⟨s.filter (fun i => f i ∈ B.1),
    Finset.mem_powerset.mpr (Finset.filter_subset _ _)⟩
  left_inv A := by
    apply Subtype.ext
    ext i
    constructor
    · intro hi
      obtain ⟨_,hm⟩ := Finset.mem_filter.mp hi
      obtain ⟨j,hj,hji⟩ := Finset.mem_map.mp hm
      have hji' : j=i := f.injective hji
      simpa only [hji'] using hj
    · intro hi
      exact Finset.mem_filter.mpr ⟨(Finset.mem_powerset.mp A.2) hi,
        Finset.mem_map.mpr ⟨i,hi,rfl⟩⟩
  right_inv B := by
    apply Subtype.ext
    ext p
    constructor
    · intro hp
      obtain ⟨i,hi,hip⟩ := Finset.mem_map.mp hp
      simpa only [hip] using (Finset.mem_filter.mp hi).2
    · intro hp
      obtain ⟨i,hi,hip⟩ := Finset.mem_map.mp ((Finset.mem_powerset.mp B.2) hp)
      exact Finset.mem_map.mpr ⟨i,Finset.mem_filter.mpr ⟨hi,by simpa only [hip] using hp⟩,hip⟩

variable {P : Type} [Fintype P] [DecidableEq P]
variable (old : List P) (zero : P → Prop) [DecidablePred zero] (hn : old.Nodup)

def sourceOriginalOldGetEmbedding434 : Fin old.length ↪ P :=
  ⟨old.get,List.nodup_ofFn.mp (by simpa only [List.ofFn_get] using hn)⟩

theorem source_original_G_old_zero_atom_map434 :
    (zeroOld old zero).map (sourceOriginalOldGetEmbedding434 old hn) =
      old.toFinset.filter zero := by
  ext p
  constructor
  · intro hp
    obtain ⟨i,hi,hip⟩ := Finset.mem_map.mp hp
    change old.get i=p at hip
    refine Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr ?_,?_⟩
    · rw [←hip]
      exact List.get_mem old i
    · rw [←hip]
      exact (Finset.mem_filter.mp hi).2
  · intro hp
    obtain ⟨hi,hz⟩ := Finset.mem_filter.mp hp
    obtain ⟨i,hip⟩ := List.mem_iff_get.mp (List.mem_toFinset.mp hi)
    exact Finset.mem_map.mpr ⟨i,Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,by simpa only [hip] using hz⟩,hip⟩

def sourceOriginalGhostOldAtomEquiv434 :
    {A : Finset (Fin old.length) // A ∈ (zeroOld old zero).powerset} ≃
      {A : Finset P // A ∈ (old.toFinset.filter zero).powerset} :=
  (sourceOriginalSubsetEmbeddingEquiv434 (zeroOld old zero)
    (sourceOriginalOldGetEmbedding434 old hn)).trans
      (Equiv.subtypeEquiv (Equiv.refl _) (fun A => by
        rw [source_original_G_old_zero_atom_map434 old zero hn]
        rfl))

abbrev SourceOriginalGhostAtomChoice434 :=
  {A : Finset P // A ∈ (old.toFinset.filter zero).powerset} × Finset P

def sourceOriginalGhostAtomEquiv434 :
    SourceOriginalGhostSetChoice434 old zero ≃ SourceOriginalGhostAtomChoice434 old zero :=
  Equiv.prodCongr (sourceOriginalGhostOldAtomEquiv434 old zero hn) (Equiv.refl _)

theorem source_original_G_old_atom_card434
    (A : {A : Finset (Fin old.length) // A ∈ (zeroOld old zero).powerset}) :
    ((sourceOriginalGhostOldAtomEquiv434 old zero hn A).1).card=A.1.card := by
  exact Finset.card_map _

include hn in
theorem source_original_G_zero_atom_card434 :
    (old.toFinset.filter zero).card=(zeroOld old zero).card := by
  rw [←source_original_G_old_zero_atom_map434 old zero hn,Finset.card_map]

/-- OLD deletion is transported to actual atom subsets with its exact
survivor multiset, rather than an assumed cardinality pushforward. -/
theorem source_original_G_old_atom_survivors434
    (A : Finset (Fin old.length)) :
    memoryTupleBag (fun j : {j : Fin old.length // j ∉ A} => old.get j) =
      ∑ p ∈ old.toFinset \ A.map (sourceOriginalOldGetEmbedding434 old hn),
        ({p}:Multiset P) := by
  unfold memoryTupleBag
  apply Finset.sum_bij (fun j _ => old.get j.val)
  · intro j hj
    apply Finset.mem_sdiff.mpr
    refine ⟨List.mem_toFinset.mpr (List.get_mem old j.val),?_⟩
    intro h
    obtain ⟨i,hi,hij⟩ := Finset.mem_map.mp h
    have hij' : i=j.val := (sourceOriginalOldGetEmbedding434 old hn).injective hij
    exact j.property (by simpa only [hij'] using hi)
  · intro i hi j hj hij
    apply Subtype.ext
    exact (sourceOriginalOldGetEmbedding434 old hn).injective hij
  · intro p hp
    obtain ⟨hpo,hpa⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨i,hip⟩ := List.mem_iff_get.mp (List.mem_toFinset.mp hpo)
    refine ⟨⟨i,?_⟩,Finset.mem_univ _,hip⟩
    intro hi
    exact hpa (Finset.mem_map.mpr ⟨i,hi,hip⟩)
  · intro j hj
    rfl
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSourceEWeightActive -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- The literal oriented BIG E weight at rho=1. All dependence on the
OLD residues, their number, the store set and the OLD injection disappears
from this coefficient. Legality and the output remain separate data. -/
theorem source_original_ORIENTED_E_rho_one_weight434
    {P : Type} [Fintype P] [DecidableEq P]
    (modulus : P → ℕ) [∀ p,NeZero (modulus p)] (M B : ℕ)
    (mu : P → ℝ) (V : ℝ) (x : BigState modulus M B)
    (target : Fin M → P) (shared : Finset (Fin M))
    (sigma tau : Equiv.Perm (Fin M)) (step : ℤ)
    (c : BigEdgeChoice modulus M B x) :
    orientedBigBranchCoefficient modulus M B mu V 1 x target shared sigma tau step c =
      (1:ℂ)/(V:ℂ)^c.2.1.card *
        ∏ j ∈ orientedFresh M shared c.2.1,(mu (target (tau j)):ℂ) := by
  simp only [orientedBigBranchCoefficient,Complex.ofReal_one,one_pow,one_mul]

theorem source_original_ORIENTED_E_rho_one_OLD_independent434
    {P : Type} [Fintype P] [DecidableEq P]
    (modulus : P → ℕ) [∀ p,NeZero (modulus p)] (M B B' : ℕ)
    (mu : P → ℝ) (V : ℝ) (x : BigState modulus M B) (x' : BigState modulus M B')
    (target : Fin M → P) (shared : Finset (Fin M))
    (sigma sigma' tau : Equiv.Perm (Fin M)) (step step' : ℤ)
    (c : BigEdgeChoice modulus M B x) (c' : BigEdgeChoice modulus M B' x')
    (hp : c.2.1=c'.2.1) :
    orientedBigBranchCoefficient modulus M B mu V 1 x target shared sigma tau step c =
    orientedBigBranchCoefficient modulus M B' mu V 1 x' target shared sigma' tau step' c' := by
  rw [source_original_ORIENTED_E_rho_one_weight434,
    source_original_ORIENTED_E_rho_one_weight434,hp]

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap cap' : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- The actual full source E coefficient is independent of the OLD
background at rho=1 when its active endpoints, pattern, auxiliary draws,
permutations and promoted target positions are fixed. The complete joint
Knu, both source phases, source divisor and SMALL factor are retained.
No claim about a correspondence of legal witnesses is made here. -/
theorem source_original_SOURCE_E_rho_one_active_weight434
    (q : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (x : FullPhysicalState SP sm BP bm (J+ell) cap)
    (x' : FullPhysicalState SP sm BP bm (J+ell) cap')
    (nu : Nu) (aux : SourceBigAux BP J m (patterns nu))
    (b : FullPhysicalEdgeBranch SP sm BP bm (J+ell) cap x)
    (b' : FullPhysicalEdgeBranch SP sm BP bm (J+ell) cap' x')
    (ss tt : Green64SmallHaar.GroupPermFamily (G := SG) (J+ell))
    (hs : x.1=x'.1) (hb : ∀ g,(x.2 g).1=(x'.2 g).1)
    (hsi : b.sigmaBig=b'.sigmaBig) (hti : b.tauBig=b'.tauBig)
    (hst : b.smallTarget=b'.smallTarget)
    (ht : ∀ g,(b.bigChoice g).1=(b'.bigChoice g).1)
    (hp : ∀ g,(b.bigChoice g).2.2.1=(b'.bigChoice g).2.2.1) :
    sourceOrientedPhysicalCoefficient SP sm BP bm J ell m cap patterns
      q 1 Vs V mu K zeta theta o k x ⟨nu,aux,b,ss,tt⟩ =
    sourceOrientedPhysicalCoefficient SP sm BP bm J ell m cap' patterns
      q 1 Vs V mu K zeta theta o k x' ⟨nu,aux,b',ss,tt⟩ := by
  simp only [sourceOrientedPhysicalCoefficient,sourceOrientedStep,
    sourceOrientedPhysicalD,orientedBigBranchCoefficient,
    Complex.ofReal_one,one_pow,one_mul]
  simp_rw [hs,hb,hsi,hti,hst,ht,hp]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalPhysicalEPromotionUnique -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- At fixed promoted target positions, the OLD injection is unique
whenever OLD prime labels are distinct. -/
theorem source_original_ORIENTED_E_promotion_injection_unique434
    {P : Type} [Fintype P] [DecidableEq P]
    (modulus : P → ℕ) [∀ p,NeZero (modulus p)] (M B : ℕ)
    (x : BigState modulus M B)
    (hi : Function.Injective (fun j : Fin x.2.1.val => (x.2.2 j).1))
    (target : Fin M → P) (tau : Equiv.Perm (Fin M))
    (promote : Finset (Fin M))
    (f g : ↥promote ↪ Fin x.2.1.val)
    (hf : ∀ j : ↥promote,target (tau j.val)=(x.2.2 (f j)).1)
    (hg : ∀ j : ↥promote,target (tau j.val)=(x.2.2 (g j)).1) : f=g := by
  apply Function.Embedding.ext
  intro j
  exact hi ((hf j).symm.trans (hg j))

/-- The entire literal legal OLD-injection fibre is empty or a singleton.
This includes the true source zero, divisibility, store and capacity tests. -/
theorem source_original_ORIENTED_E_legal_injection_subsingleton434
    {P : Type} [Fintype P] [DecidableEq P]
    (modulus : P → ℕ) [∀ p,NeZero (modulus p)] (M B : ℕ)
    (x : BigState modulus M B)
    (hi : Function.Injective (fun j : Fin x.2.1.val => (x.2.2 j).1))
    (target : Fin M → P) (shared : Finset (Fin M))
    (sigma tau : Equiv.Perm (Fin M)) (D : ℕ) (step : ℤ)
    (store promote : Finset (Fin M)) :
    Subsingleton {f : ↥promote ↪ Fin x.2.1.val //
      OrientedBigEdgeLegal modulus M B x target shared sigma tau D step
        ⟨store,promote,f⟩} := by
  constructor
  intro f g
  apply Subtype.ext
  exact source_original_ORIENTED_E_promotion_injection_unique434 modulus M B
    x hi target tau promote f.1 g.1 f.2.promoted_matches g.2.promoted_matches

/-- Exact collapse of the actual oriented E injection sum, for an arbitrary
joint test H of the complete physical witness. There is no OLD-cardinality
factor and no supposition that H separates. -/
theorem source_original_ORIENTED_E_legal_injection_sum434
    {P : Type} [Fintype P] [DecidableEq P]
    (modulus : P → ℕ) [∀ p,NeZero (modulus p)] (M B : ℕ)
    (x : BigState modulus M B)
    (hi : Function.Injective (fun j : Fin x.2.1.val => (x.2.2 j).1))
    (target : Fin M → P) (shared : Finset (Fin M))
    (sigma tau : Equiv.Perm (Fin M)) (D : ℕ) (step : ℤ)
    (store promote : Finset (Fin M))
    (H : BigEdgeChoice modulus M B x → ℂ) :
    (∑ f : ↥promote ↪ Fin x.2.1.val,
      if OrientedBigEdgeLegal modulus M B x target shared sigma tau D step
          ⟨store,promote,f⟩ then H ⟨store,promote,f⟩ else 0) =
    if h : ∃ f : ↥promote ↪ Fin x.2.1.val,
        OrientedBigEdgeLegal modulus M B x target shared sigma tau D step
          ⟨store,promote,f⟩ then
      H ⟨store,promote,Classical.choose h⟩ else 0 := by
  classical
  by_cases h : ∃ f : ↥promote ↪ Fin x.2.1.val,
      OrientedBigEdgeLegal modulus M B x target shared sigma tau D step
        ⟨store,promote,f⟩
  · rw [dif_pos h]
    let f := Classical.choose h
    have hf : OrientedBigEdgeLegal modulus M B x target shared sigma tau D step
        ⟨store,promote,f⟩ := Classical.choose_spec h
    rw [Finset.sum_eq_single f]
    · exact if_pos hf
    · intro g hg hgf
      apply if_neg
      intro hlegal
      exact hgf (source_original_ORIENTED_E_promotion_injection_unique434 modulus M B
        x hi target tau promote g f hlegal.promoted_matches hf.promoted_matches)
    · intro hf
      exact False.elim (hf (Finset.mem_univ f))
  · rw [dif_neg h]
    apply Finset.sum_eq_zero
    intro f hf
    exact if_neg (fun hf => h ⟨f,hf⟩)

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (M : ℕ) (cap : BG → ℕ)

/-- The uniqueness premise is a theorem on every reachable source state,
including after all actual G/E transitions. -/
theorem source_original_PHYSICAL_reachable_OLD_injective434
    (x : FullPhysicalState SP sm BP bm M cap) (seen : Finset ℕ)
    (hx : sourceOriginalPhysicalReachable434 SP sm BP bm M
      (physicalFockProjection SP sm BP bm M cap x) seen) (g : BG) :
    Function.Injective (fun j : Fin (x.2 g).2.1.val => ((x.2 g).2.2 j).1) := by
  have hh := (source_original_PHYSICAL_reachable_pending434 SP sm BP bm M cap x seen hx).1 g
  apply List.nodup_ofFn.mp
  simpa only [fockToList,List.map_ofFn,Function.comp_def] using hh

/-- Applied literal E injection sum on the proved reachable source sector.
No extra distinctness, norm or separability hypothesis is introduced. -/
theorem source_original_PHYSICAL_reachable_E_injection_sum434
    (x : FullPhysicalState SP sm BP bm M cap) (seen : Finset ℕ)
    (hx : sourceOriginalPhysicalReachable434 SP sm BP bm M
      (physicalFockProjection SP sm BP bm M cap x) seen) (g : BG)
    (target : Fin M → BP g) (shared : Finset (Fin M))
    (sigma tau : Equiv.Perm (Fin M)) (D : ℕ) (step : ℤ)
    (store promote : Finset (Fin M))
    (H : BigEdgeChoice (bm g) M (cap g) (x.2 g) → ℂ) :
    (∑ f : ↥promote ↪ Fin (x.2 g).2.1.val,
      if OrientedBigEdgeLegal (bm g) M (cap g) (x.2 g) target shared sigma tau D step
          ⟨store,promote,f⟩ then H ⟨store,promote,f⟩ else 0) =
    if h : ∃ f : ↥promote ↪ Fin (x.2 g).2.1.val,
        OrientedBigEdgeLegal (bm g) M (cap g) (x.2 g) target shared sigma tau D step
          ⟨store,promote,f⟩ then
      H ⟨store,promote,Classical.choose h⟩ else 0 :=
  source_original_ORIENTED_E_legal_injection_sum434 (bm g) M (cap g) (x.2 g)
    (source_original_PHYSICAL_reachable_OLD_injective434 SP sm BP bm M cap x seen hx g)
    target shared sigma tau D step store promote H
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSourceEFrame -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 18000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- Actual source E data with the OLD-index injections omitted. All
endpoints, permutations, pattern, auxiliary labels, store sets and
promoted target positions are retained. This carrier is independent
of the number of pending OLD atoms and of the Fock caps. -/
abbrev SourceOriginalSourceEFrame434 :=
  Σ nu : Nu, SourceBigAux BP J m (patterns nu) ×
    ((BigGroupPerm (BG := BG) (J+ell)) ×
      (BigGroupPerm (BG := BG) (J+ell)) ×
      ((g : BG) → (Fin (J+ell) → BP g) ×
        Finset (Fin (J+ell)) × Finset (Fin (J+ell))) ×
      Green64SmallHaar.GroupState SP sm (J+ell)) ×
    Green64SmallHaar.GroupPermFamily (G := SG) (J+ell) ×
    Green64SmallHaar.GroupPermFamily (G := SG) (J+ell)

noncomputable instance :
    Fintype (SourceOriginalSourceEFrame434 SP sm BP J ell m patterns) := by
  letI (nu : Nu) : Fintype (SourceBigAux BP J m (patterns nu)) := inferInstance
  letI : Fintype (BigGroupPerm (BG := BG) (J+ell)) := inferInstance
  letI : Fintype ((g : BG) → (Fin (J+ell) → BP g) × Finset (Fin (J+ell)) × Finset (Fin (J+ell))) := inferInstance
  letI : Fintype (Green64SmallHaar.GroupState SP sm (J+ell)) := inferInstance
  letI : Fintype (Green64SmallHaar.GroupPermFamily (G := SG) (J+ell)) := inferInstance
  unfold SourceOriginalSourceEFrame434
  infer_instance

def sourceOriginalSourceEFrame434
    (x : FullPhysicalState SP sm BP bm (J+ell) cap)
    (z : FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x) :
    SourceOriginalSourceEFrame434 SP sm BP J ell m patterns :=
  ⟨z.1,z.2.1,
    (z.2.2.1.sigmaBig,z.2.2.1.tauBig,
      fun g => ((z.2.2.1.bigChoice g).1,
        (z.2.2.1.bigChoice g).2.1,(z.2.2.1.bigChoice g).2.2.1),
      z.2.2.1.smallTarget),
    z.2.2.2.1,z.2.2.2.2⟩

abbrev SourceOriginalSourceEFrameInjections434
    (x : FullPhysicalState SP sm BP bm (J+ell) cap)
    (r : SourceOriginalSourceEFrame434 SP sm BP J ell m patterns) :=
  (g : BG) → ↥((r.2.2.1.2.2.1 g).2.2) ↪ Fin (x.2 g).2.1.val

def sourceOriginalSourceEFrameLift434
    (x : FullPhysicalState SP sm BP bm (J+ell) cap)
    (r : SourceOriginalSourceEFrame434 SP sm BP J ell m patterns)
    (f : SourceOriginalSourceEFrameInjections434 SP sm BP bm J ell m cap patterns x r) :
    FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x :=
  ⟨r.1,r.2.1,{
    sigmaBig := r.2.2.1.1
    tauBig := r.2.2.1.2.1
    bigChoice := fun g => ⟨(r.2.2.1.2.2.1 g).1,
      (r.2.2.1.2.2.1 g).2.1,(r.2.2.1.2.2.1 g).2.2,f g⟩
    smallTarget := r.2.2.1.2.2.2 },
    r.2.2.2.1,r.2.2.2.2⟩

def sourceOriginalSourceEFrameEquiv434
    (x : FullPhysicalState SP sm BP bm (J+ell) cap) :
    FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x ≃
      Σ r : SourceOriginalSourceEFrame434 SP sm BP J ell m patterns,
        SourceOriginalSourceEFrameInjections434 SP sm BP bm J ell m cap patterns x r where
  toFun z := ⟨sourceOriginalSourceEFrame434 SP sm BP bm J ell m cap patterns x z,
    fun g => (z.2.2.1.bigChoice g).2.2.2⟩
  invFun z := sourceOriginalSourceEFrameLift434 SP sm BP bm J ell m cap patterns x z.1 z.2
  left_inv := by
    rintro ⟨nu,aux,b,ss,tt⟩
    cases b with
    | mk si ta bc st =>
      dsimp only [sourceOriginalSourceEFrame434,sourceOriginalSourceEFrameLift434]
  right_inv := by
    rintro ⟨r,f⟩
    rcases r with ⟨nu,aux,b,ss,tt⟩
    rcases b with ⟨si,ta,bc,st⟩
    dsimp only [sourceOriginalSourceEFrame434,sourceOriginalSourceEFrameLift434]

/-- All-group legal injections are unique on the actual reachable sector.
The fixed frame still carries every source arithmetic and phase datum. -/
theorem source_original_SOURCE_E_frame_injections_unique434
    (x : FullPhysicalState SP sm BP bm (J+ell) cap) (seen : Finset ℕ)
    (hx : sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell)
      (physicalFockProjection SP sm BP bm (J+ell) cap x) seen)
    (r : SourceOriginalSourceEFrame434 SP sm BP J ell m patterns) (o k : ℤ)
    (f g : SourceOriginalSourceEFrameInjections434 SP sm BP bm J ell m cap patterns x r)
    (hf : sourceOrientedPhysicalLegal SP sm BP bm J ell m cap patterns x o k
      (sourceOriginalSourceEFrameLift434 SP sm BP bm J ell m cap patterns x r f))
    (hg : sourceOrientedPhysicalLegal SP sm BP bm J ell m cap patterns x o k
      (sourceOriginalSourceEFrameLift434 SP sm BP bm J ell m cap patterns x r g)) :
    f=g := by
  funext i
  exact source_original_ORIENTED_E_promotion_injection_unique434 (bm i) (J+ell) (cap i)
    (x.2 i)
    (source_original_PHYSICAL_reachable_OLD_injective434 SP sm BP bm (J+ell) cap x seen hx i)
    (r.2.2.1.2.2.1 i).1 (r.2.2.1.2.1 i) (r.2.2.1.2.2.1 i).2.2
    (f i) (g i) (hf.2.2.2.1 i).promoted_matches (hg.2.2.2.1 i).promoted_matches
end Green64Analytic.CorrelationSquare

end

end

