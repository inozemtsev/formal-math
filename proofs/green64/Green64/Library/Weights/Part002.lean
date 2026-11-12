module

public import Green64.Library.Weights.Part001
public import Mathlib.Tactic
public import Mathlib
public import Green64.Library.Analysis.PrimeNumberTheorem.Part003
public import Mathlib.Data.Finset.Image

@[expose] public section

/-!
# Weights / Part002

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## G2ActualGrowth -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime
theorem g2_actual_LFunction_disk_growth :
∀ (C C₅ δ₀ : ℝ), 0 < C → 0 ≤ C₅ → 0 < δ₀ →
  ∃ L₀ : ℝ, 3 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L →
    let Q : ℝ := 3*L^C
    let V : ℝ := 3*Real.exp (3*L)
    let D : ℝ := 10.5*Real.log Q +
      61.5*(Real.log V)^(2/3:ℝ)*(Real.log (Real.log V))^(1/3:ℝ)
    let δ : ℝ := (100*D)⁻¹
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      (q:ℝ) ≤ L^C → ∀ (t y : ℝ) (w : ℂ),
        L^(C₅+3) ≤ |t| → |t| ≤ (Real.exp L)^2 →
        |y| ≤ L^C₅ →
        ‖w - (((1+δ:ℝ):ℝ):ℂ) - ((y-t:ℝ):ℂ)*Complex.I‖ ≤ 8*δ →
        Real.log ‖DirichletCharacter.LFunction χ w‖ ≤
          50*(Real.log L + δ*L) :=
by
  intro C C₅ δ₀ hC hC₅ hδ₀
  obtain ⟨L₁,hL₁,hGrowth⟩ := eventual_source_disk_growth C
  obtain ⟨L₂,hL₂,hParam⟩ := g2_all_source_parameters C C₅ δ₀ hC hC₅ hδ₀
  refine ⟨max L₁ L₂, hL₂.trans (le_max_right _ _), ?_⟩
  intro L hL Q V D δ q inst χ hq t y w htlo hthi hy hw
  have hL₁' : L₁ ≤ L := (le_max_left _ _).trans hL
  have hL₂' : L₂ ≤ L := (le_max_right _ _).trans hL
  have hp := hParam L hL₂'
  change 0 < δ ∧ δ < δ₀ ∧ δ ≤ 1/100 ∧ L⁻¹ ≤ δ ∧
    Real.log L ≤ δ*L ∧
    -50*Real.log L ≤ Real.log δ-Real.log 2 ∧
    100*δ*D = 1 ∧
    (∀ (q : ℕ), (q:ℝ) ≤ L^C → 3*(q:ℝ) ≤ Q) ∧
    (∀ (t y : ℝ), L^(C₅+3) ≤ |t| → |t| ≤ (Real.exp L)^2 →
        |y| ≤ L^C₅ →
        20+L^C₅ ≤ |t| ∧ 20 ≤ |y-t| ∧
        |y-t| ≤ 2*(Real.exp L)^2 ∧
        |t|+L^C₅+8*δ ≤ V) at hp
  rcases hp with ⟨hδpos,_,hδmax,_,_,_,_,_,hFreq⟩
  obtain ⟨_,hVlower,hVupper,_⟩ := hFreq t y htlo hthi hy
  exact hGrowth q χ L δ (y-t) w
    hL₁' hδpos hδmax hVlower hVupper hw hq
end Green64Analytic.LongPrime

end

/-! ## GeometricKernel -/

section

namespace Green64SourceC6

/-- Exact geometric-kernel bound for a unit-circle phase, including z=1. -/
theorem geometric_unit_kernel (z : ℂ) (N : ℕ) (hz : ‖z‖ = 1) :
    ‖∑ n ∈ Finset.range N, z^n‖ ≤ (N : ℝ) ∧
    ‖1 - z‖ * ‖∑ n ∈ Finset.range N, z^n‖ ≤ 2 := by
  have hfirst : ‖∑ n ∈ Finset.range N, z^n‖ ≤ (N : ℝ) := by
    calc
      _ ≤ ∑ n ∈ Finset.range N, ‖z^n‖ := norm_sum_le _ _
      _ = ∑ n ∈ Finset.range N, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro n hn
        simp [norm_pow, hz]
      _ = (N : ℝ) := by simp
  have hgeom :
      ‖∑ n ∈ Finset.range N, z^n‖ * ‖1-z‖ = ‖1-z^N‖ := by
    rw [← norm_mul, geom_sum_mul_neg]
  have hpow : ‖z^N‖ = 1 := by simp [norm_pow, hz]
  have hsecond : ‖1-z^N‖ ≤ 2 := by
    calc
      _ ≤ ‖(1 : ℂ)‖ + ‖z^N‖ := norm_sub_le _ _
      _ = 2 := by norm_num [hpow]
  refine ⟨hfirst, ?_⟩
  rw [mul_comm, hgeom]
  exact hsecond

end Green64SourceC6

end

/-! ## GhostOperatorFinite -/

section

open scoped BigOperators
open Classical

namespace Green64MemoryGhostOp

variable {P : Type} [Fintype P] [DecidableEq P]

/-- Actual index set of zero residues in the incoming ordered OLD memory. -/
noncomputable def zeroOld (old : List P) (atZero : P → Prop)
    [DecidablePred atZero] : Finset (Fin old.length) :=
  Finset.univ.filter (fun j => atZero (old.get j))

/-- Remove the selected OLD indices, never a newly born particle.
    The list remains ordered. We use index-valued deletion and do not
    assume that particles have distinct numerical prime values. -/
noncomputable def afterGhost (old : List P)
    (A : Finset (Fin old.length)) {b : ℕ} (fresh : Fin b → P) : List P :=
  ((List.finRange old.length).filter (fun j => j ∉ A)).map old.get ++
    List.ofFn fresh

/-- One fully expanded source ghost-row term: separate OLD deletion,
    unmarked-zero damping and independent ordered birth integrations.
    The factor 1/b! occurs exactly ONCE, in G (never in the edge).
    The measure nu is the finite prime-law mass at each drawn label. -/
noncomputable def sourceGhostTerm (old : List P) (atZero : P → Prop)
    [DecidablePred atZero] (A : Finset (Fin old.length))
    {b : ℕ} (fresh : Fin b → P)
    (α χ γ : ℂ) (nu : P → ℂ) : ℂ :=
  α ^ A.card * χ ^ ((zeroOld old atZero).card - A.card) *
    (1 / (Nat.factorial b : ℂ)) * γ ^ b *
      (∏ j : Fin b, nu (fresh j))

/-- One group G_(i,g) from the source, cut only in the number of *new*
    ghost births b <= B. This is an operator acting on actual ordered
    memory-state test functions, not a formal weight identity premise. -/
noncomputable def finiteGhostG (old : List P) (atZero : P → Prop)
    [DecidablePred atZero] (B : ℕ)
    (α χ γ : ℂ) (nu : P → ℂ) (F : List P → ℂ) : ℂ :=
  ∑ A ∈ (zeroOld old atZero).powerset,
    ∑ b ∈ Finset.range (B+1),
      ∑ fresh : Fin b → P,
        sourceGhostTerm old atZero A fresh α χ γ nu *
          F (afterGhost old A fresh)

/-- Complete finite set of outgoing OLD-deletion/new-birth memory states.
    No finite-state assumption is made about the ambient list type. -/
noncomputable def reachableGhost (old : List P) (atZero : P → Prop)
    [DecidablePred atZero] (B : ℕ) : Finset (List P) :=
  ((zeroOld old atZero).powerset).biUnion (fun A =>
    (Finset.range (B+1)).biUnion (fun b =>
      (Finset.univ : Finset (Fin b → P)).image
        (fun fresh => afterGhost old A fresh)))

/-- The kernel is independently indexed by the TWO memory states, i.e.
    it collects all source OLD-index subsets and independent births
    leading to that ordered target. Multiple histories are summed. -/
noncomputable def finiteGhostKernel (old next : List P)
    (atZero : P → Prop) [DecidablePred atZero] (B : ℕ)
    (α χ γ : ℂ) (nu : P → ℂ) : ℂ :=
  ∑ A ∈ (zeroOld old atZero).powerset,
    ∑ b ∈ Finset.range (B+1),
      ∑ fresh : Fin b → P,
        if afterGhost old A fresh = next then
          sourceGhostTerm old atZero A fresh α χ γ nu else 0

theorem ghost_reachable (old : List P) (atZero : P → Prop)
    [DecidablePred atZero] (B : ℕ)
    (A : Finset (Fin old.length))
    (hA : A ∈ (zeroOld old atZero).powerset)
    (b : ℕ) (hb : b ∈ Finset.range (B+1))
    (fresh : Fin b → P) :
    afterGhost old A fresh ∈ reachableGhost old atZero B := by
  classical
  unfold reachableGhost
  apply Finset.mem_biUnion.mpr
  refine ⟨A,hA,?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨b,hb,?_⟩
  exact Finset.mem_image.mpr ⟨fresh,Finset.mem_univ _,rfl⟩

/-- Actual operator-to-kernel equality, retaining repeated target
    histories: this is the exact finite G row rather than assuming
    that the memory coefficient equals a physical lifespan weight. -/
theorem finiteGhostG_kernel_expansion
    (old : List P) (atZero : P → Prop) [DecidablePred atZero]
    (B : ℕ) (α χ γ : ℂ) (nu : P → ℂ)
    (F : List P → ℂ) :
    finiteGhostG old atZero B α χ γ nu F =
      ∑ next ∈ reachableGhost old atZero B,
        finiteGhostKernel old next atZero B α χ γ nu * F next := by
  classical
  unfold finiteGhostG finiteGhostKernel
  symm
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro A hA
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro fresh hfresh
  have hm := ghost_reachable old atZero B A hA b hb fresh
  simp [Finset.sum_ite_eq, hm]

end Green64MemoryGhostOp

end

/-! ## FockAtoms -/

section

open Classical
open scoped BigOperators

namespace Green64Fock

variable {P : Type} [Fintype P] [DecidableEq P]
variable {modulus : P → ℕ} [∀ p : P, NeZero (modulus p)]

/-- The source Z_g = {(p,r) : p∈P_g, r∈Z/pZ}. Unlike a probability
measure on residues, the source lambda has COUNTING measure in r. -/
abbrev Atom (P : Type) (modulus : P → ℕ) := Σ p : P, ZMod (modulus p)

def zeroAtom (p : P) : Atom P modulus := ⟨p, 0⟩

noncomputable def lambdaMass
    (nu : P → ℝ) (z : Atom P modulus) : ℝ := nu z.1

/-- Sum over *all* residues of a fixed prime. Exact source count mass
is p*nu(p), NOT nu(p) as under an erroneously uniform residue law. -/
theorem all_residues_count_mass
    (nu : P → ℝ) (p : P) :
    (∑ r : ZMod (modulus p), lambdaMass nu (⟨p,r⟩ : Atom P modulus)) =
      (modulus p : ℝ) * nu p := by
  simp [lambdaMass, ZMod.card, mul_comm]

/-- Selecting the ONE zero residue costs no extra 1/p: the measure of
(p,0) equals nu(p), even with count measure in the other p-1 residues. -/
theorem one_zero_residue_mass
    (nu : P → ℝ) (p : P) :
    lambdaMass nu (zeroAtom p : Atom P modulus) = nu p := rfl

/-- Births can only be at zero displacement, so this law vanishes on
all other residue atoms; no implicit p^-1 factor is inserted. -/
noncomputable def birthMass
    (nu : P → ℂ) (z : Atom P modulus) : ℂ :=
  if z.2 = 0 then nu z.1 else 0

theorem birthMass_zero
    (nu : P → ℂ) (p : P) :
    birthMass nu (zeroAtom p : Atom P modulus) = nu p := by
  change (if ((0 : ZMod (modulus p)) = 0) then nu p else 0) = nu p
  simp

theorem birthMass_nonzero_residue
    (nu : P → ℂ) (z : Atom P modulus)
    (hr : z.2 ≠ 0) :
    birthMass nu z = 0 := by simp [birthMass, hr]

/-- The sum over all prime-residue atoms of the zero-residue birth
law equals the original source prime-only birth sum exactly. -/
theorem birthMass_total
    (nu : P → ℂ) :
    (∑ z : Atom P modulus, birthMass nu z) = ∑ p : P, nu p := by
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro p hp
  change (∑ r : ZMod (modulus p), if r = 0 then nu p else 0) = nu p
  rw [Finset.sum_ite_eq']
  simp

end Green64Fock

end

/-! ## FiniteFockMeasure -/

section

open Classical
open scoped BigOperators

namespace Green64Fock

variable {U : Type} [Fintype U]
variable {B : ℕ}

/-- The source Fock memory is a finite cutoff of ⊕_{j≥0}
L²_sym(Z_g^j, (1/j!) lambda^⊗j). This carrier retains ORDERED
indices (including repeated numerical prime values) before passing
to the symmetric subspace. -/
abbrev FockState (U : Type) (B : ℕ) :=
  Σ j : Fin (B+1), Fin j.val → U

/-- The source finite Fock sector mass is the product counting-atom
mass divided by exactly ONE j!. The factor is Hilbert measure,
not an additional factor in each local G/E row. -/
noncomputable def fockMass
    (mu : U → ℝ) (s : FockState U B) : ℝ :=
  (∏ i : Fin s.1.val, mu (s.2 i)) /
    (Nat.factorial s.1.val : ℝ)

noncomputable def finiteFockInner
    (mu : U → ℝ) (f g : FockState U B → ℂ) : ℂ :=
  ∑ s : FockState U B,
     (fockMass mu s : ℂ) * star (f s) * g s

theorem fockMass_positive
    (mu : U → ℝ) (hmu : ∀ u : U, 0 < mu u)
    (s : FockState U B) : 0 < fockMass mu s := by
  unfold fockMass
  apply div_pos
  · apply Finset.prod_pos
    intro i hi
    exact hmu _
  · exact_mod_cast Nat.factorial_pos s.1.val

theorem fockMass_ne_zero
    (mu : U → ℝ) (hmu : ∀ u : U, 0 < mu u)
    (s : FockState U B) : (fockMass mu s : ℂ) ≠ 0 := by
  exact_mod_cast ne_of_gt (fockMass_positive mu hmu s)

/-- The right/left Fock vacuum in the j=0 sector. -/
def vacuumState (U : Type) (B : ℕ) : FockState U B :=
  ⟨⟨0,by omega⟩, fun i : Fin 0 => i.elim0⟩

theorem vacuum_fockMass (mu : U → ℝ) :
    fockMass mu (vacuumState U B) = 1 := by
  change (∏ i : Fin 0, mu i.elim0) / (Nat.factorial 0 : ℝ) = 1
  simp

/-- For an ordinary one-particle atom in B≥1, the Fock mass is
exactly its per-atom lambda mass, not an extra divided-by-p mass. -/
def singleState (U : Type) (u : U) : FockState U 1 :=
  ⟨⟨1,by omega⟩, fun _ => u⟩

theorem single_fockMass (mu : U → ℝ) (u : U) :
    fockMass mu (singleState U u) = mu u := by
  change (∏ i : Fin 1, mu u) / (Nat.factorial 1 : ℝ) = mu u
  simp

/-- A genuine repeated-atom state: both particles have the SAME
atom u. No artificial Nodup restriction is used. Its ordered
mass is mu(u)^2/2!, required by the symmetric Fock measure. -/
def doubleRepeatedState (U : Type) (u : U) : FockState U 2 :=
  ⟨⟨2,by omega⟩, fun _ => u⟩

theorem doubleRepeated_fockMass (mu : U → ℝ) (u : U) :
    fockMass mu (doubleRepeatedState U u) =
      mu u ^ 2 / 2 := by
  change (∏ i : Fin 2, mu u) / (Nat.factorial 2 : ℝ) = mu u ^ 2 / 2
  simp

/-- Being physically symmetric means dependence only on the MULTISET
of actual prime/residue atoms, not on their OLD index positions. It
allows two particles with identical values and residues. -/
def IsFockSymmetric (f : FockState U B → ℂ) : Prop :=
  ∀ s t, ((List.ofFn s.2 : Multiset U) =
     (List.ofFn t.2 : Multiset U)) → f s = f t

theorem const_isFockSymmetric (c : ℂ) :
    IsFockSymmetric (U := U) (B := B) (fun _ => c) := by
  intro s t h
  rfl

/-- The symmetric Hilbert vacuum is the indicator of j=0.
There is exactly ONE j=0 vector independent of the atom type. -/
noncomputable def vacuumVector : FockState U B → ℂ :=
  fun s => if s.1.val=0 then 1 else 0

theorem vacuumVector_vacuum :
    vacuumVector (U := U) (B := B) (vacuumState U B) = 1 := by
  simp [vacuumVector,vacuumState]

theorem vacuumVector_symmetric :
    IsFockSymmetric (B := B) (vacuumVector (U := U) (B := B)) := by
  intro s t h
  have hlength : s.1.val = t.1.val := by
    have hc := congrArg Multiset.card h
    simpa using hc
  simp [vacuumVector, hlength]

end Green64Fock

end

/-! ## FockAdjointAlgebra -/

section

open Classical
open scoped BigOperators

namespace Green64Fock

/-- The literal Fock mass ratio is REAL, so conjugation leaves it
unchanged; multiplying by the target mass cancels its denominator.
This is the exact scalar identity behind a weighted Hilbert adjoint. -/
theorem adjoint_scalar_identity
    (mx my : ℝ) (hy : my ≠ 0) (K f g : ℂ) :
    (my:ℂ) * star (((mx:ℂ)/(my:ℂ))*star K*f) * g =
      (mx:ℂ)*star f*K*g := by
  have hyC : (my:ℂ) ≠ 0 := by exact_mod_cast hy
  have hratio : star ((mx : ℂ) / (my : ℂ)) =
      (mx : ℂ)/(my : ℂ) := by simp
  simp only [star_mul,star_star, hratio]
  field_simp

/-- The finite Hilbert source adjoint identity for any kernel and a
positive nonuniform atom/sector measure. No symmetry, counting,
or already postulated adjoint assertion is assumed. -/
theorem finite_weighted_kernel_adjoint_identity
    {S : Type} [Fintype S]
    (m : S → ℝ) (hm : ∀ s : S, m s ≠ 0)
    (K : S → S → ℂ) (f g : S → ℂ) :
    (∑ x : S, (m x : ℂ) * star (f x) *
        (∑ y : S, K x y * g y)) =
    (∑ y : S, (m y : ℂ) *
        star (∑ x : S,
          ((m x : ℂ)/(m y : ℂ))*star (K x y)*f x) * g y) := by
  classical
  calc
    (∑ x : S, (m x : ℂ) * star (f x) *
        (∑ y : S, K x y * g y)) =
      ∑ x : S, ∑ y : S,
        ((m x : ℂ) * star (f x) * K x y * g y) := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro y hy
          ring
    _ = ∑ y : S, ∑ x : S,
          ((m x : ℂ) * star (f x) * K x y * g y) := Finset.sum_comm
    _ = ∑ y : S, (m y : ℂ) *
        star (∑ x : S,
          ((m x : ℂ)/(m y : ℂ))*star (K x y)*f x) * g y := by
          apply Finset.sum_congr rfl
          intro y hy
          rw [star_sum]
          rw [Finset.mul_sum]
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro x hx
          exact (adjoint_scalar_identity
            (m x) (m y) (hm y) (K x y) (f x) (g y)).symm

end Green64Fock

end

/-! ## FiniteFockGhost -/

section

open Classical
open scoped BigOperators

namespace Green64Fock

variable {U : Type} [Fintype U] [DecidableEq U]
variable {B : ℕ}

/-- View a single finite Fock sector as an ordered OLD memory list.
This is the actual sector coordinate, not the distinct-value support. -/
def fockToList (x : FockState U B) : List U := List.ofFn x.2

theorem fockToList_length (x : FockState U B) :
    (fockToList x).length = x.1.val := by simp [fockToList]

/-- The exact source raw G_(i,g) OLD-index/fresh-birth kernel restricted
to Fock sectors of at most B memory particles. All repeated atoms are
retained and the source raw ghost term includes one factor 1/b!. -/
noncomputable def fockGhostKernel
    (zero : U → Prop) [DecidablePred zero]
    (α χ γ : ℂ) (nu : U → ℂ)
    (x y : FockState U B) : ℂ :=
  Green64MemoryGhostOp.finiteGhostKernel
    (fockToList x) (fockToList y) zero B α χ γ nu

noncomputable def ghostRow
    (zero : U → Prop) [DecidablePred zero]
    (α χ γ : ℂ) (nu : U → ℂ)
    (g : FockState U B → ℂ) : FockState U B → ℂ :=
  fun x => ∑ y : FockState U B,
    fockGhostKernel zero α χ γ nu x y * g y

/-- Restriction to the finite memory sector is a projection after
the actual raw G operation; no additional Fock factorials occur in
its transition kernel. -/
theorem ghostRow_eq_kernel_sum
    (zero : U → Prop) [DecidablePred zero]
    (α χ γ : ℂ) (nu : U → ℂ)
    (g : FockState U B → ℂ) (x : FockState U B) :
    ghostRow zero α χ γ nu g x =
      ∑ y : FockState U B,
        Green64MemoryGhostOp.finiteGhostKernel
          (fockToList x) (fockToList y) zero B α χ γ nu * g y := rfl

/-- The L² formal adjoint with the ACTUAL source symmetric Fock
sector measure m(z)=(1/j!)*prod lambda(z_h). Critically the joint
adjoint factor contains m(x)/m(y), not merely conjugate(K_yx).
This implements the factorial adjoint measure instead of adding
a wrong 1/j! into every transition. -/
noncomputable def ghostAdjointRow
    (mu : U → ℝ) (hmu : ∀ u : U, 0 < mu u)
    (zero : U → Prop) [DecidablePred zero]
    (α χ γ : ℂ) (nu : U → ℂ)
    (f : FockState U B → ℂ) : FockState U B → ℂ :=
  fun y => ∑ x : FockState U B,
    ((fockMass mu x : ℂ) / (fockMass mu y : ℂ)) *
      star (fockGhostKernel zero α χ γ nu x y) * f x

/-- Explicit source ghost adjoint's ratio is well-defined because
every finite Fock sector atom has strictly positive measure, even
when its numerical prime/residue atom is repeated. -/
theorem ghostAdjoint_denominator_nonzero
    (mu : U → ℝ) (hmu : ∀ u : U, 0 < mu u)
    (y : FockState U B) :
    (fockMass mu y : ℂ) ≠ 0 := fockMass_ne_zero mu hmu y

/-- This is a REAL, not postulated, finite Fock Hilbert kernel
pairing. Completeness of the unrestricted direct-sum Hilbert
operator remains a separate analytic obligation. -/
theorem finiteFockGhost_adjoint_pairing
    (mu : U → ℝ) (hmu : ∀ u : U, 0 < mu u)
    (zero : U → Prop) [DecidablePred zero]
    (α χ γ : ℂ) (nu : U → ℂ)
    (f g : FockState U B → ℂ) :
    finiteFockInner mu f (ghostRow zero α χ γ nu g) =
      finiteFockInner mu (ghostAdjointRow mu hmu zero α χ γ nu f) g := by
  simpa [finiteFockInner, ghostRow, ghostAdjointRow] using
    (finite_weighted_kernel_adjoint_identity
       (fockMass (B := B) mu)
       (fun s => ne_of_gt (fockMass_positive mu hmu s))
       (fockGhostKernel (B := B) zero α χ γ nu) f g)

end Green64Fock

end

/-! ## FockFactorialAdjoint -/

section

open Classical
open scoped BigOperators

namespace Green64Fock

variable {U : Type} [Fintype U]
variable {B : ℕ}

noncomputable def orderedAtomProduct
    (mu : U → ℝ) (s : FockState U B) : ℂ :=
  ∏ i : Fin s.1.val, (mu (s.2 i) : ℂ)

theorem orderedAtomProduct_ne_zero
    (mu : U → ℝ) (hmu : ∀ u : U, 0 < mu u)
    (s : FockState U B) : orderedAtomProduct mu s ≠ 0 := by
  unfold orderedAtomProduct
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  exact_mod_cast (ne_of_gt (hmu _))

theorem fockMass_cast
    (mu : U → ℝ) (s : FockState U B) :
    (fockMass mu s : ℂ) =
      orderedAtomProduct mu s / (Nat.factorial s.1.val : ℂ) := by
  unfold fockMass orderedAtomProduct
  push_cast
  rfl

/-- This is exactly the factorial-ratio measure in the RAW ghost
Hilbert adjoint. Its prefactor is |targetMemory|! / |oldMemory|!,
not its reciprocal. All actual atom-weight ratios remain visible,
so no illicit uniform-residue or equal-prime assumptions are used. -/
theorem fockAdjoint_ratio_exact
    (mu : U → ℝ) (hmu : ∀ u : U, 0 < mu u)
    (x y : FockState U B) :
    ((fockMass mu x : ℂ)/(fockMass mu y : ℂ)) =
      ((Nat.factorial y.1.val : ℂ) /
        (Nat.factorial x.1.val : ℂ)) *
       (orderedAtomProduct mu x / orderedAtomProduct mu y) := by
  rw [fockMass_cast, fockMass_cast]
  have hx : (Nat.factorial x.1.val : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero x.1.val
  have hy : (Nat.factorial y.1.val : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero y.1.val
  have hp : orderedAtomProduct mu y ≠ 0 :=
    orderedAtomProduct_ne_zero mu hmu y
  field_simp

/-- Both vacuum and any finite repeated-atom sector have nonzero mass,
so all the factorial adjoint ratios used in finiteFockGhost_adjoint_pairing
are genuine field divisions, not invalid 0/0 defaults. -/
theorem fockAdjoint_weight_ratio_nonzero
    (mu : U → ℝ) (hmu : ∀ u : U, 0 < mu u)
    (x y : FockState U B) :
    ((fockMass mu x : ℂ)/(fockMass mu y : ℂ)) ≠ 0 := by
  apply div_ne_zero
  · exact fockMass_ne_zero mu hmu x
  · exact fockMass_ne_zero mu hmu y

end Green64Fock

end

/-! ## MemoryGhostSurvivorBag -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64Fock
set_option maxHeartbeats 0
variable {I U : Type} [DecidableEq I] [DecidableEq U]

/-- A nodup INDEX list may carry arbitrarily repeated particle values. -/
theorem memory_bag_map_index_list (L : List I) (hL : L.Nodup) (f : I → U) :
    (L.map f : Multiset U) = ∑ i ∈ L.toFinset, ({f i} : Multiset U) := by
  induction L with
  | nil => simp
  | cons i L ih =>
    have hn : i ∉ L := (List.nodup_cons.mp hL).1
    have ht := (List.nodup_cons.mp hL).2
    simp only [List.map_cons, List.toFinset_cons]
    rw [Finset.sum_insert (by simpa using hn)]
    change ({f i} : Multiset U) + (L.map f : Multiset U) = _
    rw [ih ht]

/-- Original OLD deletion output as a survivor bag plus its birth tuple.
No numerical distinctness assumption and no changed G definition. -/
theorem memory_source_afterGhost_bag [Fintype U]
    (old : List U) (A : Finset (Fin old.length)) {b : ℕ} (fresh : Fin b → U) :
    (Green64MemoryGhostOp.afterGhost old A fresh : Multiset U) =
      memoryTupleBag (fun j : {j : Fin old.length // j ∉ A} => old.get j) + memoryTupleBag fresh := by
  change ((((List.finRange old.length).filter (fun j => j ∉ A)).map old.get : List U) : Multiset U) +
    (List.ofFn fresh : Multiset U) = _
  rw [← memory_tuple_bag_ofFn fresh]
  congr 1
  rw [memory_bag_map_index_list _ ((List.nodup_finRange old.length).filter _) old.get]
  have hs : ((List.finRange old.length).filter (fun j => j ∉ A)).toFinset =
      Finset.univ.filter (fun j => j ∉ A) := by ext j; simp
  rw [hs]
  exact Finset.sum_subtype _ (by simp) (fun j => ({old.get j} : Multiset U))

/-- The original survival exponent after deleting zero OLD indices is exactly
the zero count of the survivor tuple, including repeated zero atoms. -/
theorem memory_source_survivor_zero_count [Fintype I] (x : I → U)
    (zero : U → Prop) [DecidablePred zero] (A : Finset I)
    (hA : A ⊆ Finset.univ.filter (fun j => zero (x j))) :
    (Finset.univ.filter (fun j : I => zero (x j))).card - A.card =
      Fintype.card {j : {i : I // i ∉ A} // zero (x j)} := by
  let Z := Finset.univ.filter (fun j : I => zero (x j))
  let e : ↥(Z \ A) ≃ {j : {i : I // i ∉ A} // zero (x j)} :=
    { toFun := fun j => ⟨⟨j.1, (Finset.mem_sdiff.mp j.2).2⟩,
        (Finset.mem_filter.mp (Finset.mem_sdiff.mp j.2).1).2⟩
      invFun := fun j => ⟨j.1.1, Finset.mem_sdiff.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, j.2⟩, j.1.2⟩⟩
      left_inv := by intro j; rfl
      right_inv := by intro j; rfl }
  have h := Fintype.card_congr e
  simpa only [Fintype.card_coe, Z, Finset.card_sdiff_of_subset hA] using h
end Green64Fock

end

end

/-! ## PhysicalGhostPrimeSetBridge -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

/-- Physical G_i's exact source OLD-index deletion and fresh-ghost
birth formula after forgetting residue coordinates, with arbitrary
repeated OLD values still permitted. No value-level deletion is
assumed before proving injectivity from distinct births. -/
theorem ghost_actual_value_support
    {U P : Type} [DecidableEq P]
    (old : List U) (A : Finset (Fin old.length))
    {b : ℕ} (fresh : Fin b → U) (value : U → P) :
    ((Green64MemoryGhostOp.afterGhost old A fresh).map
       value).toFinset =
      ((Finset.univ : Finset (Fin old.length)) \ A).image
        (fun i => value (old.get i)) ∪
      (Finset.univ : Finset (Fin b)).image
        (fun i => value (fresh i)) := by
  classical
  ext v
  simp [Green64MemoryGhostOp.afterGhost, List.map_append,
    List.mem_toFinset, List.mem_map, List.mem_filter,
    List.mem_finRange, List.mem_ofFn, Finset.mem_image]

end Green64FullPhysicalE

end

/-! ## PhysicalGTermSourceSubset -/

section

open Classical

namespace Green64FullPhysicalE

/-- An actual ghost termination always deletes one of the OLD
physical pending indices. This is exactly the source condition
Terminated_i ⊆ Pending_i, preserving prime values and no
assumptions on multiplicity. -/
theorem ghost_actual_terminated_subset_pending
    {U P : Type} [DecidableEq P] (old : List U)
    (A : Finset (Fin old.length)) (value : U → P) :
    A.image (fun i => value (old.get i)) ⊆
      (old.map value).toFinset := by
  classical
  intro v hv
  rcases Finset.mem_image.mp hv with ⟨i, _, hi⟩
  exact List.mem_toFinset.mpr
    (List.mem_map.mpr ⟨old.get i, List.get_mem old i, hi⟩)

end Green64FullPhysicalE

end

/-! ## PhysicalGhostPrimeSetInjective -/

section

open Classical

namespace Green64FullPhysicalE

/-- Source BIG G index deletion becomes literal prime-VALUE
deletion on the actual simple-particle locus, where the old
prime-value indexing is injective. Duplicates remain allowed in
the ambient Fock sector, so this premise must not be omitted. -/
theorem ghost_actual_value_support_injective
    {U P : Type} [DecidableEq P]
    (old : List U) (A : Finset (Fin old.length))
    {b : ℕ} (fresh : Fin b → U) (value : U → P)
    (hinj : Function.Injective
      (fun j : Fin old.length => value (old.get j))) :
    ((Green64MemoryGhostOp.afterGhost old A fresh).map
       value).toFinset =
      ((old.map value).toFinset \
        A.image (fun j => value (old.get j))) ∪
      (Finset.univ : Finset (Fin b)).image
        (fun j => value (fresh j)) := by
  classical
  have hsource :
      ((Finset.univ : Finset (Fin old.length)).image
        (fun j => value (old.get j))) =
      (old.map value).toFinset := by
    ext v
    constructor
    · intro h
      rcases Finset.mem_image.mp h with ⟨j, _, hv⟩
      exact List.mem_toFinset.mpr
        (List.mem_map.mpr ⟨old.get j, List.get_mem old j, hv⟩)
    · intro hv
      rcases List.mem_map.mp (List.mem_toFinset.mp hv) with
        ⟨u, hu, hv⟩
      rcases List.mem_iff_get.mp hu with ⟨j, hj⟩
      exact Finset.mem_image.mpr
        ⟨j, Finset.mem_univ _, by rw [hj, hv]⟩
  rw [ghost_actual_value_support,
    Finset.image_sdiff Finset.univ A hinj, hsource]

end Green64FullPhysicalE

end

/-! ## PhysicalGhostVacuumTerminal -/

section

open Classical

namespace Green64FullPhysicalE

/-- A true G_N row has EMPTY outgoing Fock memory iff every
OLD pending index terminates and its ghost birth batch is empty.
The terminal physical vacuum therefore introduces NO orphan
birth at the final visit. This holds even with repeated OLD atoms. -/
theorem original_ghost_empty_output_exact
    {U : Type} (old : List U)
    (A : Finset (Fin old.length)) {b : ℕ}
    (fresh : Fin b → U) :
    Green64MemoryGhostOp.afterGhost old A fresh = [] ↔
      A = Finset.univ ∧ b = 0 := by
  classical
  constructor
  · intro h
    have hh :
        ((List.finRange old.length).filter (fun j => j ∉ A)).map
          old.get ++ List.ofFn fresh = [] := h
    rcases List.append_eq_nil_iff.mp hh with ⟨hOld,hFresh⟩
    have hb : b = 0 := by
      have hn := congrArg List.length hFresh
      simpa using hn
    have hA : A = Finset.univ := by
      ext j
      simp only [Finset.mem_univ, iff_true]
      by_contra hnot
      have hj : j ∈ (List.finRange old.length).filter
          (fun j => j ∉ A) := by
        simp [hnot]
      have hval : old.get j ∈
          ((List.finRange old.length).filter
            (fun k => k ∉ A)).map old.get :=
        List.mem_map.mpr ⟨j,hj,rfl⟩
      rw [hOld] at hval
      simp at hval
    exact ⟨hA,hb⟩
  · rintro ⟨hA,hb⟩
    subst b
    simp [Green64MemoryGhostOp.afterGhost, hA]

end Green64FullPhysicalE

end

/-! ## SourceFiniteFock -/

section

open Classical
open scoped BigOperators

namespace Green64Fock

variable {P : Type} [Fintype P] [DecidableEq P]
variable {modulus : P → ℕ} [∀ p : P, NeZero (modulus p)]
variable {B : ℕ}

/-- The ACTUAL source atom mass λ(p,r)=mu(p) for EVERY residue r
(counting residues). Hence zero residue costs mu(p), not mu(p)/p. -/
noncomputable def sourceAtomMu
    (mu : P → ℝ) : Atom P modulus → ℝ := lambdaMass mu

/-- The raw G births at residue 0 only. The assigned birth law on
the full prime-residue atom pool is the source prime-only ν law
extended by zero to nonzero residues. -/
noncomputable def sourceBirthNu
    (nu : P → ℂ) : Atom P modulus → ℂ := birthMass nu

noncomputable def sourceFockGhost
    (α χ γ : ℂ) (nu : P → ℂ)
    (g : FockState (Atom P modulus) B → ℂ) :
    FockState (Atom P modulus) B → ℂ :=
  ghostRow (fun z : Atom P modulus => z.2 = 0)
    α χ γ (sourceBirthNu nu) g

noncomputable def sourceFockGhostAdjoint
    (mu : P → ℝ) (hmu : ∀ p : P, 0 < mu p)
    (α χ γ : ℂ) (nu : P → ℂ)
    (f : FockState (Atom P modulus) B → ℂ) :
    FockState (Atom P modulus) B → ℂ :=
  ghostAdjointRow (sourceAtomMu mu) (fun z => hmu z.1)
    (fun z : Atom P modulus => z.2 = 0)
    α χ γ (sourceBirthNu nu) f

theorem sourceFock_hilbert_ghost_adjoint
    (mu : P → ℝ) (hmu : ∀ p : P, 0 < mu p)
    (α χ γ : ℂ) (nu : P → ℂ)
    (f g : FockState (Atom P modulus) B → ℂ) :
    finiteFockInner (sourceAtomMu mu) f
       (sourceFockGhost α χ γ nu g) =
    finiteFockInner (sourceAtomMu mu)
       (sourceFockGhostAdjoint mu hmu α χ γ nu f) g := by
  exact finiteFockGhost_adjoint_pairing
     (sourceAtomMu mu) (fun z => hmu z.1)
     (fun z : Atom P modulus => z.2=0)
     α χ γ (sourceBirthNu nu) f g

/-- The first source ghost particle born at (p,0) is given the
exact λ(p,0) weight mu(p) by the Fock Hilbert inner product. -/
theorem sourceFock_single_zero_atom_mass
    (mu : P → ℝ) (p : P) :
    fockMass (sourceAtomMu mu)
      (singleState (Atom P modulus) (zeroAtom p)) = mu p :=
  single_fockMass (sourceAtomMu mu) (zeroAtom p)

/-- TWO indistinguishable (p,0) atoms are physically allowed in
the enlarged Fock space. Their sector mass is mu(p)^2/2. The
restriction to globally distinct births is imposed on paths
separately, not built into the symmetric Hilbert state space. -/
theorem sourceFock_duplicate_zero_atom_mass
    (mu : P → ℝ) (p : P) :
    fockMass (sourceAtomMu mu)
      (doubleRepeatedState (Atom P modulus) (zeroAtom p)) =
      mu p ^ 2 / 2 :=
  doubleRepeated_fockMass (sourceAtomMu mu) (zeroAtom p)

/-- An inadmissible birth of (p,r) with r≠0 contributes ZERO in
the actual raw G sum even when the old memory contains
other particles with repeated numerical prime values. -/
theorem sourceG_wrong_residue_birth_vanishes
    (old : List (Atom P modulus))
    (A : Finset (Fin old.length)) {b : ℕ}
    (fresh : Fin b → Atom P modulus) (j : Fin b)
    (hr : (fresh j).2 ≠ 0)
    (α χ γ : ℂ) (nu : P → ℂ) :
    Green64MemoryGhostOp.sourceGhostTerm old
      (fun z : Atom P modulus => z.2 = 0)
      A fresh α χ γ (sourceBirthNu nu) = 0 := by
  unfold Green64MemoryGhostOp.sourceGhostTerm
  have hz : sourceBirthNu nu (fresh j) = 0 := by
    exact birthMass_nonzero_residue nu (fresh j) hr
  have hprod : (∏ i : Fin b, sourceBirthNu nu (fresh i)) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    exact hz
  simp [hprod]

/-- The true source zero-residue integral of a birth is precisely
the prime-index ν integral, even in the finite Fock atom pool. -/
theorem sourceG_birth_total_mass
    (nu : P → ℂ) :
    (∑ z : Atom P modulus, sourceBirthNu nu z) =
      ∑ p : P, nu p := birthMass_total nu

end Green64Fock

end

/-! ## SymmetricFockOrbits -/

section

open Classical
open scoped BigOperators

namespace Green64Fock

variable {U : Type} [Fintype U] [DecidableEq U]
variable {B : ℕ}

/-- Genuine physically symmetric memory state: a MULTISET of
prime-residue atoms, retaining all repetitions. The canonical sector
support is the image of ordered FockState under multiset projection. -/
noncomputable def fockMultiset (s : FockState U B) : Multiset U :=
  (List.ofFn s.2 : Multiset U)

noncomputable def orbitSupport : Finset (Multiset U) :=
  (Finset.univ : Finset (FockState U B)).image fockMultiset

noncomputable def orbitMass
    (mu : U → ℝ) (m : Multiset U) : ℝ :=
  ∑ s ∈ (Finset.univ : Finset (FockState U B))
      with fockMultiset s = m, fockMass mu s

/-- Source Fock mass of any ordered configuration is invariant
under every particle-coordinate permutation, including repeated atoms.
This is the exact prerequisite for the symmetric Fock quotient. -/
theorem fockMass_multiset_eq
    (mu : U → ℝ) (s t : FockState U B)
    (h : fockMultiset s = fockMultiset t) :
    fockMass mu s = fockMass mu t := by
  have hsize : s.1.val = t.1.val := by
    have hc := congrArg Multiset.card h
    simpa [fockMultiset] using hc
  have hprod :
      (∏ i : Fin s.1.val, mu (s.2 i)) =
        (∏ i : Fin t.1.val, mu (t.2 i)) := by
    have hm := congrArg (fun m : Multiset U => (m.map mu).prod) h
    simpa [fockMultiset, Multiset.map_coe, Multiset.prod_coe,
      List.map_ofFn, List.prod_ofFn] using hm
  unfold fockMass
  rw [hprod, hsize]

theorem orbitMass_positive
    (mu : U → ℝ) (hmu : ∀ u : U, 0 < mu u)
    (m : Multiset U) (hm : m ∈ orbitSupport (U := U) (B := B)) :
    0 < orbitMass (B := B) mu m := by
  rcases Finset.mem_image.mp hm with ⟨s,hs,hsm⟩
  unfold orbitMass
  apply Finset.sum_pos
  · intro x hx
    exact fockMass_positive mu hmu x
  · exact ⟨s, Finset.mem_filter.mpr ⟨hs,hsm⟩⟩

/-- The finite source symmetric Fock inner pairing on unique
multiset orbits, with the TRUE orbit mass inherited from 1/j! per
ordered tuple; no uninformed artificial distinctness or 1/p factor. -/
noncomputable def symmetricFockInner
    (mu : U → ℝ) (f g : Multiset U → ℂ) : ℂ :=
  ∑ m ∈ orbitSupport (U := U) (B := B),
    (orbitMass (B := B) mu m : ℂ) * star (f m) * g m

/-- A general exact finite fibre disintegration without any
injectivity assumption on the map from ordered states to multisets. -/
theorem finite_sum_by_image
    {A C : Type} [DecidableEq C]
    (S : Finset A) (q : A → C) (w : A → ℂ) :
    (∑ s ∈ S, w s) =
      ∑ m ∈ S.image q, ∑ s ∈ S with q s = m, w s := by
  classical
  calc
    (∑ s ∈ S, w s) =
      ∑ s ∈ S, ∑ m ∈ S.image q, if q s = m then w s else 0 := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [Finset.sum_ite_eq]
      have hm : q s ∈ S.image q := Finset.mem_image.mpr ⟨s,hs,rfl⟩
      simp [hm]
    _ = ∑ m ∈ S.image q, ∑ s ∈ S, if q s = m then w s else 0 :=
      Finset.sum_comm
    _ = ∑ m ∈ S.image q, ∑ s ∈ S with q s = m, w s := by
      simp_rw [Finset.sum_filter]

/-- Exact equality between the finite ordered-sector Hilbert pairing
restricted to physically symmetric functions, and its unique-multiset
orbit Hilbert pairing. Orbit masses are DERIVED by the full
preimage sum; there is no assumed factorial cancellation. -/
theorem finite_symmetric_Fock_inner_exact
    (mu : U → ℝ) (f g : Multiset U → ℂ) :
    finiteFockInner (B := B) mu (fun s => f (fockMultiset s))
      (fun s => g (fockMultiset s)) =
      symmetricFockInner (B := B) mu f g := by
  unfold finiteFockInner symmetricFockInner
  rw [finite_sum_by_image (Finset.univ : Finset (FockState U B))
    fockMultiset (fun s => (fockMass mu s : ℂ) *
     star (f (fockMultiset s)) * g (fockMultiset s))]
  apply Finset.sum_congr rfl
  intro m hm
  calc
    (∑ s ∈ (Finset.univ : Finset (FockState U B))
      with fockMultiset s = m,
        (fockMass mu s : ℂ) *
          star (f (fockMultiset s)) * g (fockMultiset s)) =
      ∑ s ∈ (Finset.univ : Finset (FockState U B))
        with fockMultiset s = m,
          (fockMass mu s : ℂ) * (star (f m) * g m) := by
        apply Finset.sum_congr rfl
        intro s hs
        have hms : fockMultiset s = m := (Finset.mem_filter.mp hs).2
        rw [hms]
        ring
    _ = (∑ s ∈ (Finset.univ : Finset (FockState U B))
          with fockMultiset s = m,
             (fockMass mu s : ℂ)) * (star (f m) * g m) := by
        rw [Finset.sum_mul]
    _ = (orbitMass (B := B) mu m : ℂ) * star (f m) * g m := by
        simp [orbitMass, mul_assoc]

end Green64Fock

end

/-! ## FockOrbitAverage -/

section

open Classical
open scoped BigOperators

namespace Green64Fock

variable {U : Type} [Fintype U] [DecidableEq U]
variable {B : ℕ}

/-- Exact multiset orbit fibre of the ordered finite Fock space. -/
noncomputable def orbitFibre (m : Multiset U) :
    Finset (FockState U B) :=
  (Finset.univ : Finset (FockState U B)).filter
    (fun s => fockMultiset s = m)

theorem orbitFibre_nonempty
    (m : Multiset U) (hm : m ∈ orbitSupport (U := U) (B := B)) :
    (orbitFibre (U := U) (B := B) m).Nonempty := by
  rcases Finset.mem_image.mp hm with ⟨s,hs,hsm⟩
  exact ⟨s,Finset.mem_filter.mpr ⟨hs,hsm⟩⟩

/-- Canonical finite conditional expectation from arbitrary ordered
Fock functions to symmetric multiset functions. It weights each
ordered realization by its genuine Fock 1/j! sector measure. -/
noncomputable def weightedOrbitAverage
    (mu : U → ℝ) (h : FockState U B → ℂ) : Multiset U → ℂ :=
  fun m =>
    (∑ s ∈ orbitFibre (U := U) (B := B) m,
       (fockMass mu s : ℂ) * h s) /
      (orbitMass (B := B) mu m : ℂ)

/-- The explicit quotient average recovers every symmetric test
function from its ordered lift; the proof uses actual positive
mass of each orbit, not a postulated probability normalization. -/
theorem average_symmetric_lift
    (mu : U → ℝ) (hmu : ∀ u : U, 0 < mu u)
    (f : Multiset U → ℂ)
    (m : Multiset U) (hm : m ∈ orbitSupport (U := U) (B := B)) :
    weightedOrbitAverage (B := B) mu (fun s => f (fockMultiset s)) m =
      f m := by
  have hpos : (orbitMass (B := B) mu m : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (orbitMass_positive (B := B) mu hmu m hm))
  unfold weightedOrbitAverage
  have hsum :
      (∑ s ∈ orbitFibre (U := U) (B := B) m,
        (fockMass mu s : ℂ) * f (fockMultiset s)) =
      (orbitMass (B := B) mu m : ℂ) * f m := by
    calc
      _ = ∑ s ∈ orbitFibre (U := U) (B := B) m,
          (fockMass mu s : ℂ) * f m := by
            apply Finset.sum_congr rfl
            intro s hs
            rw [(Finset.mem_filter.mp hs).2]
      _ = (∑ s ∈ orbitFibre (U := U) (B := B) m,
            (fockMass mu s : ℂ)) * f m := by rw [Finset.sum_mul]
      _ = _ := by
        simp [orbitMass,orbitFibre]
  rw [hsum]
  exact mul_div_cancel_left₀ (f m) hpos

/-- Exact Hermitian symmetry of the ordered finite Fock Hilbert
inner form, with arbitrary real positive atom masses. -/
theorem finiteFockInner_star
    (mu : U → ℝ) (f g : FockState U B → ℂ) :
    star (finiteFockInner mu f g) = finiteFockInner mu g f := by
  unfold finiteFockInner
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro s hs
  have hm : star (fockMass mu s : ℂ) = (fockMass mu s : ℂ) := by simp
  simp only [star_mul,star_star,hm]
  ring

theorem symmetricFockInner_star
    (mu : U → ℝ) (f g : Multiset U → ℂ) :
    star (symmetricFockInner (B := B) mu f g) =
      symmetricFockInner (B := B) mu g f := by
  unfold symmetricFockInner
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hmass :
      star (orbitMass (B := B) mu m : ℂ) =
        (orbitMass (B := B) mu m : ℂ) := by simp
  simp only [star_mul,star_star,hmass]
  ring

/-- The TRUE symmetric Fock quotient pairing is an exact conditional
expectation of the raw ordered Fock Hilbert pairing. Thus the
symmetric subspace is not defined by removing repeated prime values. -/
theorem weightedOrbitAverage_pairing
    (mu : U → ℝ) (hmu : ∀ u : U, 0 < mu u)
    (f : Multiset U → ℂ) (h : FockState U B → ℂ) :
    symmetricFockInner (B := B) mu f
      (weightedOrbitAverage (B := B) mu h) =
    finiteFockInner mu (fun s => f (fockMultiset s)) h := by
  unfold symmetricFockInner finiteFockInner
  rw [finite_sum_by_image (Finset.univ : Finset (FockState U B))
      fockMultiset
      (fun s => (fockMass mu s : ℂ) *
        star (f (fockMultiset s)) * h s)]
  apply Finset.sum_congr rfl
  intro m hm
  have hnonzero : (orbitMass (B := B) mu m : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (orbitMass_positive (B := B) mu hmu m hm))
  unfold weightedOrbitAverage
  change (orbitMass (B := B) mu m : ℂ) * star (f m) *
      ((∑ s ∈ orbitFibre (U := U) (B := B) m,
        (fockMass mu s : ℂ) * h s) / (orbitMass (B := B) mu m : ℂ)) =
    (∑ s ∈ orbitFibre (U := U) (B := B) m,
       (fockMass mu s : ℂ) *
         star (f (fockMultiset s)) * h s)
  have hsum :
      (∑ s ∈ orbitFibre (U := U) (B := B) m,
        (fockMass mu s : ℂ) *
          star (f (fockMultiset s)) * h s) =
      star (f m) *
        (∑ s ∈ orbitFibre (U := U) (B := B) m,
          (fockMass mu s : ℂ) * h s) := by
    calc
      _ = ∑ s ∈ orbitFibre (U := U) (B := B) m,
            star (f m) * ((fockMass mu s : ℂ) * h s) := by
              apply Finset.sum_congr rfl
              intro s hs
              have hms := (Finset.mem_filter.mp hs).2
              rw [hms]
              ring
      _ = _ := by rw [Finset.mul_sum]
  rw [hsum]
  field_simp

theorem weightedOrbitAverage_pairing_right
    (mu : U → ℝ) (hmu : ∀ u : U, 0 < mu u)
    (h : FockState U B → ℂ) (g : Multiset U → ℂ) :
    symmetricFockInner (B := B) mu
      (weightedOrbitAverage (B := B) mu h) g =
    finiteFockInner mu h (fun s => g (fockMultiset s)) := by
  have hl := weightedOrbitAverage_pairing (B := B) mu hmu g h
  have hc := congrArg star hl
  rw [symmetricFockInner_star, finiteFockInner_star] at hc
  exact hc

end Green64Fock

end

/-! ## SymmetricFockGhost -/

section

open Classical
open scoped BigOperators

namespace Green64Fock

variable {U : Type} [Fintype U] [DecidableEq U]
variable {B : ℕ}

/-- True finite symmetric Fock G operator: lift a symmetric multiset
test to ordered memory, apply the source raw G kernel, then take the
Hilbert-orthogonal conditional expectation back to multiset orbits.
This construction DOES NOT assume raw G preserves the symmetric
subspace before compression; that stronger property is a separate
source-operator instantiation obligation. -/
noncomputable def symmetricGhostRow
    (mu : U → ℝ) (zero : U → Prop) [DecidablePred zero]
    (α χ γ : ℂ) (nu : U → ℂ)
    (F : Multiset U → ℂ) : Multiset U → ℂ :=
  weightedOrbitAverage (B := B) mu
    (ghostRow (B := B) zero α χ γ nu
      (fun s => F (fockMultiset s)))

/-- The symmetric Hilbert adjoint is obtained with the exact real
Fock 1/j! mass by applying the source raw adjoint, then projecting
to the physical multiset quotient. No extra row 1/j! inserted. -/
noncomputable def symmetricGhostAdjointRow
    (mu : U → ℝ) (hmu : ∀ u : U, 0 < mu u)
    (zero : U → Prop) [DecidablePred zero]
    (α χ γ : ℂ) (nu : U → ℂ)
    (F : Multiset U → ℂ) : Multiset U → ℂ :=
  weightedOrbitAverage (B := B) mu
    (ghostAdjointRow mu hmu zero α χ γ nu
      (fun s => F (fockMultiset s)))

/-- FINITE SYMMETRIC HILBERT ADJOINT. The three equalities use:
1) exact conditional expectation onto true symmetric orbit measure;
2) the raw source G Fock 1/j! weighted adjoint;
3) the reverse quotient conditional expectation.
No false assumption of distinct atoms, flat residue probability,
or hypothetical source Exact Memory Identity is made. -/
theorem symmetricFockGhost_adjoint
    (mu : U → ℝ) (hmu : ∀ u : U, 0 < mu u)
    (zero : U → Prop) [DecidablePred zero]
    (α χ γ : ℂ) (nu : U → ℂ)
    (F G : Multiset U → ℂ) :
    symmetricFockInner (B := B) mu F
      (symmetricGhostRow (B := B) mu zero α χ γ nu G) =
    symmetricFockInner (B := B) mu
      (symmetricGhostAdjointRow (B := B) mu hmu zero α χ γ nu F) G := by
  calc
    symmetricFockInner (B := B) mu F
        (symmetricGhostRow (B := B) mu zero α χ γ nu G) =
      finiteFockInner mu
        (fun s : FockState U B => F (fockMultiset s))
        (ghostRow zero α χ γ nu
          (fun s : FockState U B => G (fockMultiset s))) := by
          exact weightedOrbitAverage_pairing mu hmu F _
    _ = finiteFockInner mu
          (ghostAdjointRow mu hmu zero α χ γ nu
            (fun s : FockState U B => F (fockMultiset s)))
          (fun s : FockState U B => G (fockMultiset s)) := by
          exact finiteFockGhost_adjoint_pairing mu hmu
            zero α χ γ nu _ _
    _ = symmetricFockInner (B := B) mu
          (symmetricGhostAdjointRow (B := B) mu hmu zero α χ γ nu F) G := by
          exact (weightedOrbitAverage_pairing_right mu hmu _ G).symm

/-- The compression is a mathematically genuine symmetric operator:
its lifted output depends ONLY on the full multiset with multiplicities.
It is not merely symmetric in the SET of distinct prime values. -/
theorem symmetricGhostRow_multiset_invariant
    (mu : U → ℝ) (zero : U → Prop) [DecidablePred zero]
    (α χ γ : ℂ) (nu : U → ℂ) (F : Multiset U → ℂ) :
    IsFockSymmetric (B := B)
      (fun s : FockState U B =>
        symmetricGhostRow (B := B) mu zero α χ γ nu F (fockMultiset s)) := by
  intro s t h
  change symmetricGhostRow (B := B) mu zero α χ γ nu F
      (fockMultiset s) =
    symmetricGhostRow (B := B) mu zero α χ γ nu F
      (fockMultiset t)
  change fockMultiset s = fockMultiset t at h
  rw [h]

theorem symmetricGhostAdjoint_multiset_invariant
    (mu : U → ℝ) (hmu : ∀ u : U, 0 < mu u)
    (zero : U → Prop) [DecidablePred zero]
    (α χ γ : ℂ) (nu : U → ℂ) (F : Multiset U → ℂ) :
    IsFockSymmetric (B := B)
      (fun s : FockState U B =>
        symmetricGhostAdjointRow (B := B) mu hmu zero α χ γ nu F
          (fockMultiset s)) := by
  intro s t h
  change symmetricGhostAdjointRow (B := B) mu hmu zero α χ γ nu F
      (fockMultiset s) =
    symmetricGhostAdjointRow (B := B) mu hmu zero α χ γ nu F
      (fockMultiset t)
  change fockMultiset s = fockMultiset t at h
  rw [h]

end Green64Fock

end

/-! ## FockVacuumSector -/

section

open Classical
open scoped BigOperators

namespace Green64Fock

variable {U : Type} [Fintype U] [DecidableEq U]
variable {B : ℕ}

/-- The multiset vacuum is realized by the unique genuine zero-particle
Fock configuration; no ghost or prime coordinate needs to be chosen. -/
theorem fockMultiset_vacuum :
    fockMultiset (vacuumState U B) = (0 : Multiset U) := by
  simp [fockMultiset, vacuumState]

theorem fockMultiset_empty_implies_vacuum
    (s : FockState U B)
    (h : fockMultiset s = 0) :
    s = vacuumState U B := by
  have hl : s.1.val = 0 := by
    have hc := congrArg Multiset.card h
    simpa [fockMultiset] using hc
  rcases s with ⟨⟨n,hn⟩,atoms⟩
  have hn0 : n = 0 := hl
  subst n
  have hatoms : atoms = (fun i : Fin 0 => i.elim0) :=
    Subsingleton.elim _ _
  subst atoms
  simp [vacuumState]

theorem orbitFibre_vacuum_eq_singleton :
    orbitFibre (U := U) (B := B) (0 : Multiset U) =
      {vacuumState U B} := by
  ext s
  simp only [orbitFibre, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_singleton]
  constructor
  · exact fockMultiset_empty_implies_vacuum s
  · intro hs
    subst s
    exact fockMultiset_vacuum

/-- The Fock symmetric vacuum has EXACT Hilbert mass 1. In
particular the 1/j! symmetric sector measure does not introduce
a spurious zero- or infinite-particle boundary normalization. -/
theorem symmetric_vacuum_mass_one (mu : U → ℝ) :
    orbitMass (B := B) mu (0 : Multiset U) = 1 := by
  change (∑ s ∈ orbitFibre (U := U) (B := B) (0 : Multiset U),
    fockMass mu s) = 1
  rw [orbitFibre_vacuum_eq_singleton]
  simp [vacuum_fockMass]

noncomputable def symmetricVacuum : Multiset U → ℂ :=
  fun m => if m = 0 then 1 else 0

theorem symmetricVacuum_value :
    symmetricVacuum (U := U) (0 : Multiset U) = 1 := by
  simp [symmetricVacuum]

theorem symmetric_vacuum_norm_squared_one (mu : U → ℝ) :
    symmetricFockInner (B := B) mu
      (symmetricVacuum (U := U))
      (symmetricVacuum (U := U)) = 1 := by
  unfold symmetricFockInner
  have h0 : (0 : Multiset U) ∈ orbitSupport (U := U) (B := B) := by
    apply Finset.mem_image.mpr
    exact ⟨vacuumState U B,Finset.mem_univ _,fockMultiset_vacuum⟩
  have hterm (m : Multiset U) :
      (orbitMass (B := B) mu m : ℂ) *
        star (symmetricVacuum (U := U) m) *
          symmetricVacuum (U := U) m =
      if m = 0 then (orbitMass (B := B) mu m : ℂ) else 0 := by
    by_cases hm : m = 0
    · simp [hm, symmetricVacuum]
    · simp [hm, symmetricVacuum]
  have hx :
      (∑ m ∈ orbitSupport (U := U) (B := B),
        (orbitMass (B := B) mu m : ℂ) *
          star (symmetricVacuum (U := U) m) *
             symmetricVacuum (U := U) m) =
      (orbitMass (B := B) mu (0 : Multiset U) : ℂ) := by
    simp_rw [hterm]
    rw [Finset.sum_ite_eq']
    simp [h0]
  rw [hx,symmetric_vacuum_mass_one]
  norm_num

end Green64Fock

end

/-! ## EdgeFactorialLaw -/

section

open Classical
open scoped BigOperators

namespace Green64PhysicalEdge

/-- The EXACT multiplicity of choosing a subset of `a` OLD indices
and injecting its ordered promoted slots into a length-`j` source
memory is `choose j a * a!`, also if atom labels coincide.
In the real Fock (1/j!) sector, this cancels to (1/(j-a)!). -/
theorem old_injections_over_fock_factorial (j a : ℕ) (ha : a ≤ j) :
    ((Nat.choose j a * Nat.factorial a : ℕ) : ℝ) /
      (Nat.factorial j : ℝ) =
    1 / (Nat.factorial (j - a) : ℝ) := by
  have hnat := Nat.choose_mul_factorial_mul_factorial ha
  have hreal :
      (((Nat.choose j a * Nat.factorial a : ℕ) : ℝ) *
          (Nat.factorial (j - a) : ℝ)) =
      (Nat.factorial j : ℝ) := by
    exact_mod_cast hnat
  have hj : (Nat.factorial j : ℝ) ≠ 0 := by positivity
  have hk : (Nat.factorial (j-a) : ℝ) ≠ 0 := by positivity
  apply (div_eq_iff hj).2
  field_simp
  nlinarith [hreal]

/-- Source eq (edge-factorial-reversal): the number of injections
into the j old positions with a promotions, divided by the source
j! sector, equals the reverse b-store injections into j-a+b
positions divided by (j-a+b)!. No extra b! or cross-group factor. -/
theorem edge_joint_factorial_reversal
    (j a b : ℕ) (ha : a ≤ j) :
    ((Nat.choose j a * Nat.factorial a : ℕ) : ℝ) /
      (Nat.factorial j : ℝ) =
    ((Nat.choose (j-a+b) b * Nat.factorial b : ℕ) : ℝ) /
      (Nat.factorial (j-a+b) : ℝ) := by
  have hb : b ≤ j-a+b := by omega
  rw [old_injections_over_fock_factorial j a ha,
      old_injections_over_fock_factorial (j-a+b) b hb]
  have hindex : (j-a+b)-b = j-a := by omega
  rw [hindex]

theorem edge_joint_vacuum_factorial :
    ((Nat.choose 0 0 * Nat.factorial 0 : ℕ) : ℝ) /
      (Nat.factorial 0 : ℝ) = 1 := by
  norm_num

theorem edge_joint_one_promoted :
    ((Nat.choose 1 1 * Nat.factorial 1 : ℕ) : ℝ) /
      (Nat.factorial 1 : ℝ) = 1 := by
  norm_num

end Green64PhysicalEdge

end

/-! ## PhysicalMemoryTranslation -/

section

open Classical
open scoped BigOperators

namespace Green64PhysicalEdge

variable {P : Type} [Fintype P] [DecidableEq P]
variable {modulus : P → ℕ} [∀ p : P, NeZero (modulus p)]
variable {B : ℕ}

/-- Source big memory atom (p,r) translated by the ONE physical
edge shift Δ. The p coordinate is unchanged, even for r=0. -/
def translateAtom (step : ℤ)
    (z : Green64Fock.Atom P modulus) :
    Green64Fock.Atom P modulus :=
  ⟨z.1, z.2 + (step : ZMod (modulus z.1))⟩

theorem translateAtom_back (step : ℤ)
    (z : Green64Fock.Atom P modulus) :
    translateAtom (-step) (translateAtom step z) = z := by
  rcases z with ⟨p,r⟩
  change (⟨p, r + (step : ZMod (modulus p)) +
      ((-step : ℤ) : ZMod (modulus p))⟩ : Green64Fock.Atom P modulus) = ⟨p,r⟩
  simp [Int.cast_neg, add_assoc]

/-- Full physical OLD memory translation on each indexed Fock sector:
NO store, promotion, deletion or new birth in this one edge component. -/
def translateFock (step : ℤ)
    (s : Green64Fock.FockState (Green64Fock.Atom P modulus) B) :
    Green64Fock.FockState (Green64Fock.Atom P modulus) B :=
  ⟨s.1, fun i => translateAtom step (s.2 i)⟩

theorem translateFock_back (step : ℤ)
    (s : Green64Fock.FockState (Green64Fock.Atom P modulus) B) :
    translateFock (-step) (translateFock step s) = s := by
  rcases s with ⟨j,atoms⟩
  simp [translateFock,translateAtom_back]

/-- TRUE source lambda counts each residue with equal mass mu(p).
Moving its residue by Δ preserves the literal 1/j! Fock Hilbert
measure for EVERY list, including repeated prime/residue atoms. -/
theorem translateFock_preserves_source_mass
    (mu : P → ℝ) (step : ℤ)
    (s : Green64Fock.FockState (Green64Fock.Atom P modulus) B) :
    Green64Fock.fockMass (Green64Fock.sourceAtomMu mu)
      (translateFock step s) =
    Green64Fock.fockMass (Green64Fock.sourceAtomMu mu) s := by
  rfl

/-- Number of zero-residue OLD pending *indices*, with multiplicity,
before or after Δ; this count supplies precisely the source ρ factors. -/
noncomputable def oldZeroCount
    (s : Green64Fock.FockState (Green64Fock.Atom P modulus) B) : ℕ :=
  (Finset.univ.filter (fun i : Fin s.1.val => (s.2 i).2 = 0)).card

/-- The physical source big edge term where a=b=0: translation
of all OLD residues followed by both endpoint ρ dampings.
No spurious 1/p factor is charged; NO memory birth occurs. -/
noncomputable def noTransferBigKernel
    (rho : ℝ) (step : ℤ)
    (s t : Green64Fock.FockState (Green64Fock.Atom P modulus) B) : ℂ :=
  if t = translateFock step s then
    (rho : ℂ) ^ (oldZeroCount s + oldZeroCount t)
  else 0

theorem noTransferBigKernel_reverse
    (rho : ℝ) (step : ℤ)
    (s t : Green64Fock.FockState (Green64Fock.Atom P modulus) B) :
    noTransferBigKernel rho step s t =
      star (noTransferBigKernel rho (-step) t s) := by
  by_cases h : t = translateFock step s
  · have hr : s = translateFock (-step) t := by
      rw [h,translateFock_back]
    simp only [noTransferBigKernel, if_pos h, if_pos hr,
      star_pow, Complex.star_def, Complex.conj_ofReal, add_comm]
  · have hr : ¬s = translateFock (-step) t := by
      intro hback
      apply h
      calc
        t = translateFock step (translateFock (-step) t) := by
          simpa only [neg_neg] using
            (translateFock_back (-step) t).symm
        _ = translateFock step s := congrArg _ hback.symm
    simp [noTransferBigKernel,h,hr]

/-- Correct finite Hilbert weight for a fixed-source no-transfer
E component, even when the same atom repeats. -/
theorem noTransferBigKernel_weighted_reverse
    (mu : P → ℝ) (rho : ℝ) (step : ℤ)
    (s t : Green64Fock.FockState (Green64Fock.Atom P modulus) B) :
    (Green64Fock.fockMass (Green64Fock.sourceAtomMu mu) s : ℂ) *
      noTransferBigKernel rho step s t =
    (Green64Fock.fockMass (Green64Fock.sourceAtomMu mu) t : ℂ) *
      star (noTransferBigKernel rho (-step) t s) := by
  rw [← noTransferBigKernel_reverse]
  by_cases h : t = translateFock step s
  · subst t
    rw [translateFock_preserves_source_mass]
  · simp [noTransferBigKernel,h]

end Green64PhysicalEdge

end

/-! ## PhysicalEdgeJointMeasure -/

section

open Classical
open scoped BigOperators

namespace Green64PhysicalEdge

variable {P : Type} [Fintype P] [DecidableEq P]
variable {modulus : P → ℕ} [∀ p : P, NeZero (modulus p)]

/-- True source λ memory product before dividing by j!:
lambda(p,r)=mu(p) for every residue r, including zero. -/
noncomputable def atomProduct
    (mu : P → ℝ) (xs : List (Green64Fock.Atom P modulus)) : ℝ :=
  (xs.map (fun z => mu z.1)).prod

noncomputable def primeProduct (mu : P → ℝ)
    (xs : List P) : ℝ :=
  (xs.map mu).prod

/-- Source edge-joint-memory, left endpoint X:
u contains the surviving OLD indices, p the a promoted labels
whose translated OLD residue is exactly zero. -/
def sourceJointInput (step : ℤ)
    (u : List (Green64Fock.Atom P modulus))
    (promoted : List P) : List (Green64Fock.Atom P modulus) :=
  u ++ promoted.map (fun p => ⟨p, ((-step : ℤ) : ZMod (modulus p))⟩)

/-- Source edge-joint-memory, right endpoint Y:
survivors translated and b selected source active labels stored at
zero before translation. Fresh draws are separate from this memory. -/
def sourceJointOutput (step : ℤ)
    (u : List (Green64Fock.Atom P modulus))
    (stored : List P) : List (Green64Fock.Atom P modulus) :=
  u.map (translateAtom step) ++
    stored.map (fun p => ⟨p, (step : ZMod (modulus p))⟩)

theorem sourceJointInput_mass
    (mu : P → ℝ) (step : ℤ)
    (u : List (Green64Fock.Atom P modulus))
    (promoted : List P) :
    atomProduct mu (sourceJointInput step u promoted) =
    atomProduct mu u * primeProduct mu promoted := by
  simp only [atomProduct, sourceJointInput, primeProduct, List.map_append,
    List.prod_append, List.map_map]
  rfl

theorem sourceJointOutput_mass
    (mu : P → ℝ) (step : ℤ)
    (u : List (Green64Fock.Atom P modulus))
    (stored : List P) :
    atomProduct mu (sourceJointOutput step u stored) =
    atomProduct mu u * primeProduct mu stored := by
  simp only [atomProduct, sourceJointOutput, primeProduct, List.map_append,
    List.prod_append, List.map_map]
  rfl

/-- The OLD pending prime p about to promote has actual residue
-step and is precisely at zero AFTER translation. -/
theorem promoted_old_residue_hits_zero (p : P) (step : ℤ) :
    translateAtom step
      (⟨p, ((-step : ℤ) : ZMod (modulus p))⟩ :
        Green64Fock.Atom P modulus) = ⟨p,0⟩ := by
  simp [translateAtom, Int.cast_neg]

/-- A source active label stored with zero anchor is at +step in
the output memory. It cannot be read from the OLD pending list. -/
theorem stored_anchor_moves (p : P) (step : ℤ) :
    translateAtom step
      (⟨p,0⟩ : Green64Fock.Atom P modulus) =
      ⟨p, (step : ZMod (modulus p))⟩ := by
  simp [translateAtom]

/-- Exact a-old-index injections weighted by source 1/j!, with
j=k+a; this handles equal prime/residue atoms by positions. -/
theorem source_input_injection_coefficient (k a : ℕ) :
    ((Nat.choose (k+a) a * Nat.factorial a : ℕ) : ℝ) /
       (Nat.factorial (k+a) : ℝ) =
    1 / (Nat.factorial k : ℝ) := by
  have h := old_injections_over_fock_factorial (k+a) a (by omega)
  simpa [Nat.add_sub_cancel_left] using h

theorem source_output_injection_coefficient (k b : ℕ) :
    ((Nat.choose (k+b) b * Nat.factorial b : ℕ) : ℝ) /
       (Nat.factorial (k+b) : ℝ) =
    1 / (Nat.factorial k : ℝ) :=
  source_input_injection_coefficient k b

/-- The source eq (edge-joint-measure), for arbitrary survivors,
promoted and stored lists, repeated atoms fully allowed. The
a-index source promotion count (j)_a and b-index reversed store
count (k+b)_b CANCEL the respective Fock sector factorials.
Both sides become 1/k! times lambda^k(u) nu^a(p) nu^b(s).
There is no residue 1/p, no cross-group factorial, no invented
1/a! or 1/b! in row transitions. -/
theorem source_exact_joint_measure
    (mu : P → ℝ) (step : ℤ)
    (u : List (Green64Fock.Atom P modulus))
    (promoted stored : List P) :
    atomProduct mu (sourceJointInput step u promoted) *
      (((Nat.choose (u.length + promoted.length) promoted.length *
          Nat.factorial promoted.length : ℕ) : ℝ) /
        (Nat.factorial (u.length + promoted.length) : ℝ)) *
      primeProduct mu stored =
    atomProduct mu (sourceJointOutput step u stored) *
      (((Nat.choose (u.length + stored.length) stored.length *
          Nat.factorial stored.length : ℕ) : ℝ) /
        (Nat.factorial (u.length + stored.length) : ℝ)) *
      primeProduct mu promoted := by
  rw [sourceJointInput_mass,sourceJointOutput_mass,
      source_input_injection_coefficient,
      source_output_injection_coefficient]
  ring

end Green64PhysicalEdge

end

/-! ## PhysicalEdgeJointReversal -/

section

open Classical
open scoped BigOperators

namespace Green64PhysicalEdge

variable {P : Type} [Fintype P] [DecidableEq P]
variable {modulus : P → ℕ} [∀ p : P, NeZero (modulus p)]

/-- Reversing physical E changes the surviving core from u to
T_Δ u and swaps OLD promoted versus NEW stored labels.
Source direction Δ becomes -Δ, without altering numerical primes. -/
theorem sourceJointInput_reverse
    (step : ℤ) (u : List (Green64Fock.Atom P modulus))
    (stored : List P) :
    sourceJointInput (-step) (u.map (translateAtom step)) stored =
      sourceJointOutput step u stored := by
  simp [sourceJointInput,sourceJointOutput]

theorem sourceJointOutput_reverse
    (step : ℤ) (u : List (Green64Fock.Atom P modulus))
    (promoted : List P) :
    sourceJointOutput (-step) (u.map (translateAtom step)) promoted =
      sourceJointInput step u promoted := by
  simp only [sourceJointOutput, sourceJointInput]
  have hmap : List.map (translateAtom (-step))
      (List.map (translateAtom step) u) = u := by
    induction u with
    | nil => rfl
    | cons z zs ih => simp [translateAtom_back, ih]
  rw [hmap]

/-- Exactly the source endpoint rho factor for the physical
joint-memory pair X/Y, including zeros of OLD and remaining
pending atoms, not a guessed damping from an abstract kernel. -/
noncomputable def jointRhoFactor
    (rho : ℝ) (step : ℤ)
    (u : List (Green64Fock.Atom P modulus))
    (promoted stored : List P) : ℝ :=
  rho ^ ((sourceJointInput step u promoted).countP
           (fun z => z.2 = 0) +
         (sourceJointOutput step u stored).countP
           (fun z => z.2 = 0))

/-- The endpoint rho damping is *identical* on physical E reversal
including all the just-stored particles in output Y and all
OLD promoted particles in input X. -/
theorem jointRhoFactor_reverse
    (rho : ℝ) (step : ℤ)
    (u : List (Green64Fock.Atom P modulus))
    (promoted stored : List P) :
    jointRhoFactor rho step u promoted stored =
      jointRhoFactor rho (-step)
        (u.map (translateAtom step)) stored promoted := by
  unfold jointRhoFactor
  rw [sourceJointInput_reverse, sourceJointOutput_reverse]
  rw [Nat.add_comm]

/-- Full exact forward JOINT INTEGRAND for the big edge memory
variables, including source OLD matching multiplicity, Fock
factorials, counting-residue λ, transfer V^-a and both rho factors.
The independent active mark/permutation/auxiliary laws are not
included (their integration is a separate real source debt). -/
noncomputable def forwardTransferJoint
    (mu : P → ℝ) (V rho : ℝ) (step : ℤ)
    (u : List (Green64Fock.Atom P modulus))
    (promoted stored : List P) : ℝ :=
  (atomProduct mu (sourceJointInput step u promoted) *
    (((Nat.choose (u.length+promoted.length) promoted.length *
        Nat.factorial promoted.length : ℕ) : ℝ) /
        (Nat.factorial (u.length+promoted.length) : ℝ)) *
    primeProduct mu stored *
    jointRhoFactor rho step u promoted stored) /
    (V ^ promoted.length)

/-- In the reversed physical edge, the old STORES become promoted
memory labels and the old PROMOTIONS become stored labels.
The transfer coefficient is then V^-b, not V^-a. -/
noncomputable def reverseTransferJoint
    (mu : P → ℝ) (V rho : ℝ) (step : ℤ)
    (u : List (Green64Fock.Atom P modulus))
    (promoted stored : List P) : ℝ :=
  (atomProduct mu (sourceJointOutput step u stored) *
    (((Nat.choose (u.length+stored.length) stored.length *
        Nat.factorial stored.length : ℕ) : ℝ) /
        (Nat.factorial (u.length+stored.length) : ℝ)) *
    primeProduct mu promoted *
    jointRhoFactor rho step u promoted stored) /
    (V ^ stored.length)

/-- Source precise reversal ratio:
  forward * V^a = reverse * V^b.
Hence forward = reverse * V^(b-a) for V>0.
This proves the complete fixed-joint-memory coefficient ratio;
summing all physical admissible source frames is STILL missing. -/
theorem transferJoint_exact_V_reversal
    (mu : P → ℝ) (V rho : ℝ) (hV : V ≠ 0)
    (step : ℤ) (u : List (Green64Fock.Atom P modulus))
    (promoted stored : List P) :
    forwardTransferJoint mu V rho step u promoted stored *
      V ^ promoted.length =
    reverseTransferJoint mu V rho step u promoted stored *
      V ^ stored.length := by
  unfold forwardTransferJoint reverseTransferJoint
  rw [div_mul_cancel₀ _ (pow_ne_zero _ hV),
    div_mul_cancel₀ _ (pow_ne_zero _ hV)]
  have hm := source_exact_joint_measure mu step u promoted stored
  rw [hm]

end Green64PhysicalEdge

end

/-! ## PhysicalBigActiveFock -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p : P, NeZero (modulus p)]
variable (M B : ℕ)

/-- The source BIG Hilbert factor at finite cutoffs: exactly M ordered
active prime labels with mu_tilde^M, AND the source prime×ZMod(p)
pending Fock sector with 1/j! lambda^j, counting each residue. -/
abbrev BigState :=
  (Fin M → P) ×
    Green64Fock.FockState (Green64Fock.Atom P modulus) B

noncomputable instance : Fintype (BigState modulus M B) := inferInstance

/-- Actual original source active-slot L2 mass, not a proxy. -/
noncomputable def activeMass (mu : P → ℝ)
    (a : Fin M → P) : ℝ :=
  ∏ i : Fin M, mu (a i)

/-- Original BIG active × Fock Hilbert product measure. Memory j!
is charged ONLY HERE, not in any edge transition. -/
noncomputable def bigStateMass (mu : P → ℝ)
    (x : BigState modulus M B) : ℝ :=
  activeMass M mu x.1 *
    Green64Fock.fockMass (Green64Fock.sourceAtomMu mu) x.2

theorem activeMass_nonneg (mu : P → ℝ)
    (hmu : ∀ p, 0 ≤ mu p) (a : Fin M → P) :
    0 ≤ activeMass M mu a := by
  unfold activeMass
  apply Finset.prod_nonneg
  intro i hi
  exact hmu _

theorem bigStateMass_positive (mu : P → ℝ)
    (hmu : ∀ p, 0 < mu p)
    (x : BigState modulus M B) :
    0 < bigStateMass modulus M B mu x := by
  unfold bigStateMass
  apply mul_pos
  · unfold activeMass
    apply Finset.prod_pos
    intro i hi
    exact hmu (x.1 i)
  · exact Green64Fock.fockMass_positive
      (Green64Fock.sourceAtomMu mu)
      (fun z => hmu z.1) x.2

/-- Memory-vacuum boundary is independent of active prime coordinates
as in the source, and no extra Hilbert normalization appears. -/
noncomputable def bigVacuum (x : BigState modulus M B) : ℂ :=
  if x.2.1.val = 0 then 1 else 0

theorem bigStateMass_vacuum
    (mu : P → ℝ) (a : Fin M → P) :
    bigStateMass modulus M B mu
      (a,Green64Fock.vacuumState (Green64Fock.Atom P modulus) B) =
    activeMass M mu a := by
  simp [bigStateMass,Green64Fock.vacuum_fockMass]

theorem bigVacuum_value
    (a : Fin M → P) :
    bigVacuum modulus M B
      (a,Green64Fock.vacuumState (Green64Fock.Atom P modulus) B) = 1 := by
  simp [bigVacuum,Green64Fock.vacuumState]

/-- Physical (not an invented uniform measure) Hilbert pairing. -/
noncomputable def bigInner (mu : P → ℝ)
    (F H : BigState modulus M B → ℂ) : ℂ :=
  ∑ x : BigState modulus M B,
    (bigStateMass modulus M B mu x : ℂ) * star (F x) * H x

end Green64FullPhysicalE

end

/-! ## PhysicalBigEdgeChoices -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p, NeZero (modulus p)]
variable (M B : ℕ)

/-- The true source independently chosen E_i transfer data:
stores are source endpoint positions, promotions are target
endpoint positions and the injection uses ONLY OLD memory indices.
No new stored atom is in the injection domain or codomain. -/
abbrev BigEdgeChoice (x : BigState modulus M B) :=
  Finset (Fin M) ×
    (Σ t : Finset (Fin M), (↥t ↪ Fin x.2.1.val))

noncomputable instance (x : BigState modulus M B) :
    Fintype (BigEdgeChoice modulus M B x) := inferInstance

/-- Exact selected OLD pending indices, distinct by injectivity even
when their prime/residue VALUES are equal. -/
noncomputable def selectedOld
    (x : BigState modulus M B) (c : BigEdgeChoice modulus M B x) :
    Finset (Fin x.2.1.val) :=
  (Finset.univ : Finset (↥c.2.1)).image c.2.2

/-- Surviving OLD particles, preserving their actual OLD slot order. -/
noncomputable def survivorIndices
    (x : BigState modulus M B) (c : BigEdgeChoice modulus M B x) :
    Finset (Fin x.2.1.val) :=
  Finset.univ \ selectedOld modulus M B x c

/-- The exact physical E_i OLD memory translation by Δ, AFTER
deleting selected promoted OLD indices, before storing source slots. -/
noncomputable def survivors
    (x : BigState modulus M B) (step : ℤ)
    (c : BigEdgeChoice modulus M B x) :
    List (Green64Fock.Atom P modulus) :=
  (survivorIndices modulus M B x c).toList.map
    (fun i => Green64PhysicalEdge.translateAtom step (x.2.2 i))

/-- The original source store operation: take selected source
permutation slots, anchor at residue zero and translate by Δ. -/
noncomputable def newlyStored
    (x : BigState modulus M B)
    (sourcePerm : Equiv.Perm (Fin M)) (step : ℤ)
    (c : BigEdgeChoice modulus M B x) :
    List (Green64Fock.Atom P modulus) :=
  c.1.toList.map (fun i =>
    ⟨x.1 (sourcePerm i), (step : ZMod (modulus (x.1 (sourcePerm i))))⟩)

/-- Output memory is a LIST of survivors then newly stored slots.
Index multiplicity is preserved; NO numerical deduplication. -/
noncomputable def physicalPendingOutput
    (x : BigState modulus M B)
    (sourcePerm : Equiv.Perm (Fin M)) (step : ℤ)
    (c : BigEdgeChoice modulus M B x) :
    List (Green64Fock.Atom P modulus) :=
  survivors modulus M B x step c ++
    newlyStored modulus M B x sourcePerm step c

/-- The E output is tested on the actual symmetric multiset of
prime-residue atoms, not a set of distinct prime values. -/
noncomputable def physicalPendingMultiset
    (x : BigState modulus M B)
    (sourcePerm : Equiv.Perm (Fin M)) (step : ℤ)
    (c : BigEdgeChoice modulus M B x) :
    Multiset (Green64Fock.Atom P modulus) :=
  (physicalPendingOutput modulus M B x sourcePerm step c : Multiset _)

theorem selectedOld_mem_old
    (x : BigState modulus M B)
    (c : BigEdgeChoice modulus M B x)
    (i : Fin x.2.1.val)
    (h : i ∈ selectedOld modulus M B x c) :
    i ∈ (Finset.univ : Finset (Fin x.2.1.val)) :=
  Finset.mem_univ i

theorem selectedOld_card
    (x : BigState modulus M B)
    (c : BigEdgeChoice modulus M B x) :
    (selectedOld modulus M B x c).card = c.2.1.card := by
  unfold selectedOld
  rw [Finset.card_image_iff.mpr]
  · simp
  · intro i hi j hj h
    exact c.2.2.injective h

theorem pending_output_length
    (x : BigState modulus M B)
    (sourcePerm : Equiv.Perm (Fin M)) (step : ℤ)
    (c : BigEdgeChoice modulus M B x) :
    (physicalPendingOutput modulus M B x sourcePerm step c).length =
      x.2.1.val - c.2.1.card + c.1.card := by
  simp [physicalPendingOutput,survivors,newlyStored,survivorIndices,
    Finset.card_sdiff, selectedOld_card]

end Green64FullPhysicalE

end

/-! ## MemoryOriginalCleanPending -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE
set_option maxHeartbeats 0

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p, NeZero (modulus p)]
variable (M B : ℕ)

/-- All OLD indices survive when the genuine source has no
promotion slot, including repeated numerical particle values. -/
theorem memory_clean_original_all_survivors
    (x : BigState modulus M B) (c : BigEdgeChoice modulus M B x)
    (hp : c.2.1 = ∅) :
    survivorIndices modulus M B x c = Finset.univ := by
  have hsel : selectedOld modulus M B x c = ∅ := by
    ext i
    constructor
    · intro hi
      obtain ⟨a, _, _⟩ := Finset.mem_image.mp hi
      have hh : (a : Fin M) ∈ c.2.1 := a.2
      simpa [hp] using hh
    · intro hi
      simp at hi
  simp [survivorIndices, hsel]

/-- No source store slot creates any new pending atom. -/
theorem memory_clean_original_no_stores
    (x : BigState modulus M B)
    (sigma : Equiv.Perm (Fin M)) (step : ℤ)
    (c : BigEdgeChoice modulus M B x)
    (hs : c.1 = ∅) :
    newlyStored modulus M B x sigma step c = [] := by
  simp [newlyStored, hs]
/-- Mapping the complete Fin-indexed OLD particle family through
any relabelling is exactly multiset-mapping its ORIGINAL Fock orbit.
Finset enumeration does not discard duplicate particle values. -/
theorem memory_clean_full_indexed_bag
    {j : ℕ} (x : Fin j → Green64Fock.Atom P modulus)
    (f : Green64Fock.Atom P modulus → Green64Fock.Atom P modulus) :
    (↑((Finset.univ : Finset (Fin j)).toList.map
        (fun i => f (x i))) : Multiset (Green64Fock.Atom P modulus)) =
    (Green64Fock.fockMultiset
      (⟨⟨j, by omega⟩, x⟩ :
        Green64Fock.FockState (Green64Fock.Atom P modulus) j)).map f := by
  have hlist :=
    Green64Fock.memory_bag_map_index_list
      ((Finset.univ : Finset (Fin j)).toList)
      (Finset.nodup_toList _) (fun i => f (x i))
  simp only [Finset.toList_toFinset] at hlist
  rw [hlist]
  simpa only [Green64Fock.memoryTupleBag, Green64Fock.fockMultiset,
    Multiset.map_coe, List.map_ofFn, Function.comp_def] using
    (Green64Fock.memory_tuple_bag_ofFn (fun i : Fin j => f (x i)))
/-- In the literal source BIG E edge with no store or promotion,
the output pending multiset is precisely translation of ALL OLD
atoms, not a new stochastic measure or a distinct-value set. -/
theorem memory_original_clean_pending_exact
    (x : BigState modulus M B)
    (sigma : Equiv.Perm (Fin M)) (step : ℤ)
    (c : BigEdgeChoice modulus M B x)
    (hs : c.1 = ∅) (hp : c.2.1 = ∅) :
    physicalPendingMultiset modulus M B x sigma step c =
      (Green64Fock.fockMultiset x.2).map
        (Green64PhysicalEdge.translateAtom (modulus := modulus) step) := by
  have hsurv := memory_clean_original_all_survivors modulus M B x c hp
  have hstore := memory_clean_original_no_stores modulus M B x sigma step c hs
  unfold physicalPendingMultiset physicalPendingOutput
  rw [hstore]
  simp only [List.append_nil]
  unfold survivors
  rw [hsurv]
  exact memory_clean_full_indexed_bag modulus x.2.2
    (Green64PhysicalEdge.translateAtom (modulus := modulus) step)
end Green64FullPhysicalE

end

end

/-! ## PhysicalBigEdgeValidity -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p, NeZero (modulus p)]
variable (M B : ℕ)

/-- Actual unshared SOURCE slots after independently sampled
endpoint permutation; shared labels use canonical group coordinates. -/
noncomputable def unsharedSource
    (shared : Finset (Fin M))
    (sigma : Equiv.Perm (Fin M)) : Finset (Fin M) :=
  Finset.univ.filter (fun i => sigma i ∉ shared)

noncomputable def unsharedTarget
    (shared : Finset (Fin M))
    (tau : Equiv.Perm (Fin M)) : Finset (Fin M) :=
  Finset.univ.filter (fun i => tau i ∉ shared)

/-- The independent target FRESH integrations use exactly those
unshared slots that were NOT supplied by OLD pending promotions. -/
noncomputable def freshTargetSlots
    (shared : Finset (Fin M))
    (tau : Equiv.Perm (Fin M))
    (promote : Finset (Fin M)) : Finset (Fin M) :=
  unsharedTarget M shared tau \ promote

/-- Source's complete source/target BIG active + OLD Fock legal
E_i branch for a FIXED shared pattern, two sampled permutations,
auxiliary divisor D and common signed edge step Δ. -/
structure PhysicalEdgeLegal
    (x : BigState modulus M B) (target : Fin M → P)
    (shared : Finset (Fin M))
    (sigma tau : Equiv.Perm (Fin M))
    (D : ℕ) (step : ℤ)
    (c : BigEdgeChoice modulus M B x) : Prop where
  shared_copy : ∀ i ∈ shared, x.1 i = target i
  stores_unshared : c.1 ⊆ unsharedSource M shared sigma
  promotes_unshared : c.2.1 ⊆ unsharedTarget M shared tau
  promoted_matches : ∀ i : ↥c.2.1,
    target (tau i.val) = (x.2.2 (c.2.2 i)).1
  promoted_zero : ∀ i : ↥c.2.1,
    (x.2.2 (c.2.2 i)).2 +
      (step : ZMod (modulus (x.2.2 (c.2.2 i)).1)) = 0
  promoted_not_dividing : ∀ i : ↥c.2.1,
    ¬ modulus ((x.2.2 (c.2.2 i)).1) ∣ D
  stored_not_dividing : ∀ i ∈ c.1,
    ¬ modulus (x.1 (sigma i)) ∣ D
  output_within_cutoff :
    (physicalPendingOutput modulus M B x sigma step c).length ≤ B

/-- The finite list of *all* independent source physical E branches.
This is not a collection of only preselected RowValid histories. -/
noncomputable def legalPhysicalChoices
    (x : BigState modulus M B) (target : Fin M → P)
    (shared : Finset (Fin M))
    (sigma tau : Equiv.Perm (Fin M))
    (D : ℕ) (step : ℤ) :
    Finset (BigEdgeChoice modulus M B x) :=
  Finset.univ.filter
    (PhysicalEdgeLegal modulus M B x target shared sigma tau D step)

theorem legal_choice_old_zero_and_bans
    (x : BigState modulus M B) (target : Fin M → P)
    (shared : Finset (Fin M))
    (sigma tau : Equiv.Perm (Fin M))
    (D : ℕ) (step : ℤ)
    (c : BigEdgeChoice modulus M B x)
    (hc : c ∈ legalPhysicalChoices modulus M B x target shared sigma tau D step)
    (i : ↥c.2.1) :
    target (tau i.val) = (x.2.2 (c.2.2 i)).1 ∧
    (x.2.2 (c.2.2 i)).2 +
      (step : ZMod (modulus (x.2.2 (c.2.2 i)).1)) = 0 ∧
    ¬ modulus ((x.2.2 (c.2.2 i)).1) ∣ D := by
  have h := (Finset.mem_filter.mp hc).2
  exact ⟨h.promoted_matches i, h.promoted_zero i, h.promoted_not_dividing i⟩

theorem legal_fresh_slot_disjoint_promotion
    (x : BigState modulus M B) (target : Fin M → P)
    (shared : Finset (Fin M))
    (sigma tau : Equiv.Perm (Fin M))
    (D : ℕ) (step : ℤ)
    (c : BigEdgeChoice modulus M B x)
    (hc : c ∈ legalPhysicalChoices modulus M B x target shared sigma tau D step) :
    Disjoint (freshTargetSlots M shared tau c.2.1) c.2.1 := by
  exact Finset.sdiff_disjoint

/-- Under the real source constraint promotions are unshared,
fresh and promoted slots partition exactly all nonshared target
slots, with no extra restriction on duplicate prime VALUES. -/
theorem legal_target_coverage
    (x : BigState modulus M B) (target : Fin M → P)
    (shared : Finset (Fin M))
    (sigma tau : Equiv.Perm (Fin M))
    (D : ℕ) (step : ℤ)
    (c : BigEdgeChoice modulus M B x)
    (hc : c ∈ legalPhysicalChoices modulus M B x target shared sigma tau D step) :
    freshTargetSlots M shared tau c.2.1 ∪ c.2.1 =
      unsharedTarget M shared tau := by
  have h : c.2.1 ⊆ unsharedTarget M shared tau :=
    (Finset.mem_filter.mp hc).2.promotes_unshared
  exact Finset.sdiff_union_of_subset h

end Green64FullPhysicalE

end

/-! ## PhysicalBigEdgeKernel -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p, NeZero (modulus p)]
variable (M B : ℕ)

/-- Source E_i FRESH target-prime integrations:
one mu_tilde(p) for each unshared, unpromoted TARGET endpoint slot.
No birth factor is charged on shared or promoted target labels. -/
noncomputable def freshIntegration
    (mu : P → ℝ) (target : Fin M → P)
    (shared : Finset (Fin M))
    (tau : Equiv.Perm (Fin M))
    (promote : Finset (Fin M)) : ℝ :=
  ∏ i ∈ freshTargetSlots M shared tau promote,
    mu (target (tau i))

/-- True target OLD-pending zero damping AFTER promotion,
including newly stored labels at their translated residue. -/
noncomputable def outputZeroCount
    (x : BigState modulus M B)
    (sigma : Equiv.Perm (Fin M)) (step : ℤ)
    (c : BigEdgeChoice modulus M B x) : ℕ :=
  (physicalPendingOutput modulus M B x sigma step c).countP
    (fun z => z.2 = 0)

/-- The COMPLETE original BIG E-branch scalar at a fixed pattern/D:
  rho^{zeros(OLD after G)+zeros(new pending)} V^-a prod_fresh mu_tilde.
There is deliberately no Fock j! in this E row (it belongs to
the Hilbert mass), and no residue factor 1/p. -/
noncomputable def physicalBigBranchCoefficient
    (mu : P → ℝ) (V rho : ℝ)
    (x : BigState modulus M B) (target : Fin M → P)
    (shared : Finset (Fin M))
    (sigma tau : Equiv.Perm (Fin M))
    (step : ℤ)
    (c : BigEdgeChoice modulus M B x) : ℂ :=
  ((rho : ℂ) ^
    (Green64PhysicalEdge.oldZeroCount x.2 +
       outputZeroCount modulus M B x sigma step c)) *
    ((1 : ℂ) / (V : ℂ) ^ c.2.1.card) *
    (freshIntegration M mu target shared tau c.2.1 : ℂ)

/-- A source shared/free label dependent complex coefficient
K_nu D^(i zeta) exp(2pi i theta sigma kD) is supplied ONCE
per fixed frame, never multiplied separately into each group. -/
noncomputable def physicalBigSelectedCoefficient
    (mu : P → ℝ) (V rho : ℝ)
    (K : ℂ)
    (x : BigState modulus M B) (target : Fin M → P)
    (shared : Finset (Fin M))
    (sigma tau : Equiv.Perm (Fin M))
    (step : ℤ)
    (c : BigEdgeChoice modulus M B x) : ℂ :=
  K * physicalBigBranchCoefficient modulus M B mu V rho
    x target shared sigma tau step c

/-- Genuine finite target ACTIVE state and actual symmetric pending
MULTISET output; the pending multiset retains equal atom occurrences. -/
abbrev BigPhysicalOutput :=
  (Fin M → P) × Multiset (Green64Fock.Atom P modulus)

/-- Every legal branch is selected from the full finite carrier:
target active sample, store source subset, promote target subset,
inject OLD pending indices, with actual p∤D and zero tests. -/
abbrev BigPhysicalBranch (x : BigState modulus M B) :=
  (Fin M → P) × BigEdgeChoice modulus M B x

noncomputable instance (x : BigState modulus M B) :
    Fintype (BigPhysicalBranch modulus M B x) := inferInstance

noncomputable def legalPhysicalBranches
    (x : BigState modulus M B)
    (shared : Finset (Fin M))
    (sigma tau : Equiv.Perm (Fin M))
    (D : ℕ) (step : ℤ) :
    Finset (BigPhysicalBranch modulus M B x) :=
  Finset.univ.filter (fun z =>
    PhysicalEdgeLegal modulus M B x z.1 shared sigma tau D step z.2)

noncomputable def physicalBranchOutput
    (x : BigState modulus M B)
    (sigma : Equiv.Perm (Fin M)) (step : ℤ)
    (z : BigPhysicalBranch modulus M B x) :
    BigPhysicalOutput modulus M :=
  (z.1,physicalPendingMultiset modulus M B x sigma step z.2)

/-- TRUE source fixed-frame physical BIG E_i row:
sum over ALL target active labels (the independent fresh integrals)
and every admissible indexed store/promote/injection choice. -/
noncomputable def physicalBigFrameRow
    (mu : P → ℝ) (V rho : ℝ) (K : ℂ)
    (x : BigState modulus M B)
    (shared : Finset (Fin M))
    (sigma tau : Equiv.Perm (Fin M))
    (D : ℕ) (step : ℤ)
    (F : BigPhysicalOutput modulus M → ℂ) : ℂ :=
  ∑ z ∈ legalPhysicalBranches modulus M B x shared sigma tau D step,
    physicalBigSelectedCoefficient modulus M B mu V rho K
      x z.1 shared sigma tau step z.2 *
      F (physicalBranchOutput modulus M B x sigma step z)

/-- Explicit independent target-fresh sampling and OLD-choice nested
sum, with each target active tuple having the correct mass factor. -/
noncomputable def physicalBigNestedRow
    (mu : P → ℝ) (V rho : ℝ) (K : ℂ)
    (x : BigState modulus M B)
    (shared : Finset (Fin M))
    (sigma tau : Equiv.Perm (Fin M))
    (D : ℕ) (step : ℤ)
    (F : BigPhysicalOutput modulus M → ℂ) : ℂ :=
  ∑ target : Fin M → P,
    ∑ c ∈ legalPhysicalChoices modulus M B x target shared sigma tau D step,
      physicalBigSelectedCoefficient modulus M B mu V rho K
        x target shared sigma tau step c *
      F (target,physicalPendingMultiset modulus M B x sigma step c)

end Green64FullPhysicalE

end

/-! ## PhysicalBigEdgeDisintegration -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p, NeZero (modulus p)]
variable (M B : ℕ)

/-- Independently sampled target active prime arrays plus legal
OLD memory branch choices. In particular the row does NOT read a
predeclared literal SourceRow or any prechosen next-state weight. -/
theorem physicalBig_nested_eq_frame
    (mu : P → ℝ) (V rho : ℝ) (K : ℂ)
    (x : BigState modulus M B)
    (shared : Finset (Fin M))
    (sigma tau : Equiv.Perm (Fin M))
    (D : ℕ) (step : ℤ)
    (F : BigPhysicalOutput modulus M → ℂ) :
    physicalBigNestedRow modulus M B mu V rho K x shared sigma tau D step F =
      physicalBigFrameRow modulus M B mu V rho K x shared sigma tau D step F := by
  classical
  unfold physicalBigNestedRow physicalBigFrameRow
    legalPhysicalBranches legalPhysicalChoices
  simp only [Finset.sum_filter]
  rw [Fintype.sum_prod_type]
  rfl

/-- Finite Fubini over a genuinely enumerated branch space; its
output fibres retain different OLD index injections leading to the
same target multiset, including repeated physical atom values. -/
theorem sum_over_exact_output_fibres
    {A Z : Type} [DecidableEq Z]
    (choices : Finset A) (out : A → Z)
    (weight : A → ℂ) (F : Z → ℂ) :
    (∑ c ∈ choices, weight c * F (out c)) =
    ∑ z ∈ choices.image out,
      (∑ c ∈ choices, if out c = z then weight c else 0) * F z := by
  classical
  calc
    _ = ∑ c ∈ choices, ∑ z ∈ choices.image out,
      if out c = z then weight c * F z else 0 := by
        apply Finset.sum_congr rfl
        intro c hc
        rw [Finset.sum_ite_eq]
        simp [Finset.mem_image.mpr ⟨c,hc,rfl⟩]
    _ = ∑ z ∈ choices.image out, ∑ c ∈ choices,
      if out c = z then weight c * F z else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro c hc
      split_ifs <;> simp

/-- True physical BIG E fibre-support consists ONLY of outputs
reachable by the source-compliant OLD-index/store/fresh choices,
after translating all residues by the original Δ. -/
noncomputable def physicalBigOutputs
    (x : BigState modulus M B)
    (shared : Finset (Fin M))
    (sigma tau : Equiv.Perm (Fin M))
    (D : ℕ) (step : ℤ) :
    Finset (BigPhysicalOutput modulus M) :=
  (legalPhysicalBranches modulus M B x shared sigma tau D step).image
    (physicalBranchOutput modulus M B x sigma step)

/-- Full fixed-frame source BIG E_i state transition kernel obtained
by adding EVERY branch coefficient whose true physical pending
multiset and target active array agree with the queried output.
Equal outputs from different OLD-index choices are NOT deduplicated. -/
noncomputable def physicalBigStateKernel
    (mu : P → ℝ) (V rho : ℝ) (K : ℂ)
    (x : BigState modulus M B)
    (shared : Finset (Fin M))
    (sigma tau : Equiv.Perm (Fin M))
    (D : ℕ) (step : ℤ)
    (out : BigPhysicalOutput modulus M) : ℂ :=
  ∑ z ∈ legalPhysicalBranches modulus M B x shared sigma tau D step,
    if physicalBranchOutput modulus M B x sigma step z = out then
      physicalBigSelectedCoefficient modulus M B mu V rho K
        x z.1 shared sigma tau step z.2
    else 0

/-- PHYSICAL E source exact finite disintegration: the independently
sampled BIG active/OLD Fock edge row equals its real state-to-state
kernel with every distinct branch multiplicity and every original
mu_tilde, V^-a and rho factor exactly once. This does not yet sample
source D, nor prove the symmetric/infinite Hilbert adjoint. -/
theorem physicalBigFrameRow_eq_state_kernel
    (mu : P → ℝ) (V rho : ℝ) (K : ℂ)
    (x : BigState modulus M B)
    (shared : Finset (Fin M))
    (sigma tau : Equiv.Perm (Fin M))
    (D : ℕ) (step : ℤ)
    (F : BigPhysicalOutput modulus M → ℂ) :
    physicalBigFrameRow modulus M B mu V rho K
        x shared sigma tau D step F =
    ∑ out ∈ physicalBigOutputs modulus M B x shared sigma tau D step,
      physicalBigStateKernel modulus M B mu V rho K
        x shared sigma tau D step out * F out := by
  unfold physicalBigFrameRow physicalBigOutputs physicalBigStateKernel
  exact sum_over_exact_output_fibres
    (legalPhysicalBranches modulus M B x shared sigma tau D step)
    (physicalBranchOutput modulus M B x sigma step)
    (fun z => physicalBigSelectedCoefficient modulus M B mu V rho K
      x z.1 shared sigma tau step z.2) F

end Green64FullPhysicalE

end

/-! ## PhysicalActiveMeasureSplit -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {P : Type} [Fintype P] [DecidableEq P]
variable (M : ℕ)

/-- The source shared canonical slots pulled back by an independently
sampled endpoint permutation sigma. -/
noncomputable def sharedSourceSlots
    (shared : Finset (Fin M))
    (sigma : Equiv.Perm (Fin M)) : Finset (Fin M) :=
  Finset.univ.filter (fun i => sigma i ∈ shared)

/-- The shared prime LABEL product is independent of how the
source endpoint permutation enumerates the actual shared slots. -/
theorem source_shared_mass_permutation (mu : P → ℝ)
    (a : Fin M → P) (shared : Finset (Fin M))
    (sigma : Equiv.Perm (Fin M)) :
    (∏ i ∈ sharedSourceSlots M shared sigma, mu (a (sigma i))) =
    ∏ j ∈ shared, mu (a j) := by
  classical
  apply Finset.prod_bij (fun i _ => sigma i)
  · intro i hi
    simpa [sharedSourceSlots] using hi
  · intro i hi j hj heq
    exact sigma.injective heq
  · intro j hj
    refine ⟨sigma.symm j, ?_, ?_⟩
    · simpa [sharedSourceSlots] using hj
    · simp
  · intro i hi
    rfl

/-- Independently enumerated ordered active lists have the original
mu_tilde^M mass and split into EXACT shared and unshared positions. -/
theorem activeMass_shared_unshared (mu : P → ℝ)
    (a : Fin M → P) (shared : Finset (Fin M))
    (sigma : Equiv.Perm (Fin M)) :
    activeMass M mu a =
      (∏ j ∈ shared, mu (a j)) *
      (∏ i ∈ unsharedSource M shared sigma, mu (a (sigma i))) := by
  have hcompl :
      unsharedSource M shared sigma =
        (sharedSourceSlots M shared sigma)ᶜ := by
    ext i
    simp [unsharedSource,sharedSourceSlots]
  calc
    activeMass M mu a =
      ∏ i : Fin M, mu (a (sigma i)) := by
        unfold activeMass
        exact (Equiv.prod_comp sigma (fun i => mu (a i))).symm
    _ = (∏ i ∈ sharedSourceSlots M shared sigma, mu (a (sigma i))) *
      (∏ i ∈ unsharedSource M shared sigma, mu (a (sigma i))) := by
        rw [hcompl]
        exact (Finset.prod_mul_prod_compl
          (sharedSourceSlots M shared sigma)
          (fun i => mu (a (sigma i)))).symm
    _ = _ := by rw [source_shared_mass_permutation]

/-- Dividing physical input unshared source slots into stores and
drops preserves its TRUE active Hilbert measure; no extra mu for
the stored labels is inserted into E_i. -/
theorem activeMass_store_drop (mu : P → ℝ)
    (a : Fin M → P) (shared : Finset (Fin M))
    (sigma : Equiv.Perm (Fin M))
    (stores : Finset (Fin M))
    (hs : stores ⊆ unsharedSource M shared sigma) :
    activeMass M mu a =
      (∏ j ∈ shared, mu (a j)) *
      (∏ i ∈ stores, mu (a (sigma i))) *
      (∏ i ∈ unsharedSource M shared sigma \ stores,
        mu (a (sigma i))) := by
  rw [activeMass_shared_unshared M mu a shared sigma]
  have h := Finset.prod_sdiff (f := fun i => mu (a (sigma i))) hs
  rw [← h]
  ring

/-- The target active Hilbert measure splits into shared canonical
labels, promoted target slots and independently sampled FRESH slots. -/
theorem activeMass_promote_fresh (mu : P → ℝ)
    (a : Fin M → P) (shared : Finset (Fin M))
    (tau : Equiv.Perm (Fin M))
    (promote : Finset (Fin M))
    (hp : promote ⊆ unsharedTarget M shared tau) :
    activeMass M mu a =
      (∏ j ∈ shared, mu (a j)) *
      (∏ i ∈ promote, mu (a (tau i))) *
      freshIntegration M mu a shared tau promote := by
  rw [activeMass_shared_unshared M mu a shared tau]
  have h := Finset.prod_sdiff (f := fun i => mu (a (tau i))) hp
  change (∏ j ∈ shared, mu (a j)) *
    (∏ i ∈ unsharedTarget M shared tau, mu (a (tau i))) = _
  rw [← h]
  simp only [freshIntegration,freshTargetSlots]
  ring

/-- The original physical shared canonical source and target active
labels agree under the source pattern; their Hilbert shared factor
matches EXACTLY despite independent endpoint permutations. -/
theorem shared_active_mass_eq (mu : P → ℝ)
    (source target : Fin M → P) (shared : Finset (Fin M))
    (hshared : ∀ j ∈ shared, source j = target j) :
    (∏ j ∈ shared, mu (source j)) =
      ∏ j ∈ shared, mu (target j) := by
  apply Finset.prod_congr rfl
  intro j hj
  rw [hshared j hj]

end Green64FullPhysicalE

end

/-! ## PhysicalActiveJointBalance -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {P : Type} [Fintype P] [DecidableEq P]
variable (M : ℕ)

/-- Source big active slots dropped instead of stored; this is the
reverse-edge FRESH integration set, not a new particle birth measure. -/
noncomputable def droppedSourceMass
    (mu : P → ℝ) (source : Fin M → P)
    (shared : Finset (Fin M)) (sigma : Equiv.Perm (Fin M))
    (stores : Finset (Fin M)) : ℝ :=
  ∏ i ∈ unsharedSource M shared sigma \ stores, mu (source (sigma i))

noncomputable def promotedTargetList
    (target : Fin M → P) (tau : Equiv.Perm (Fin M))
    (promote : Finset (Fin M)) : List P :=
  promote.toList.map (fun i => target (tau i))

noncomputable def storedSourceList
    (source : Fin M → P) (sigma : Equiv.Perm (Fin M))
    (stores : Finset (Fin M)) : List P :=
  stores.toList.map (fun i => source (sigma i))

theorem slots_primeProduct_eq
    (mu : P → ℝ) (a : Fin M → P)
    (s : Finset (Fin M)) :
    Green64PhysicalEdge.primeProduct mu (s.toList.map a) =
      ∏ i ∈ s, mu (a i) := by
  simp [Green64PhysicalEdge.primeProduct,List.map_map]

theorem promotedTargetList_mass
    (mu : P → ℝ) (target : Fin M → P)
    (tau : Equiv.Perm (Fin M)) (promote : Finset (Fin M)) :
    Green64PhysicalEdge.primeProduct mu
      (promotedTargetList M target tau promote) =
    ∏ i ∈ promote, mu (target (tau i)) := by
  exact slots_primeProduct_eq M mu (fun i => target (tau i)) promote

theorem storedSourceList_mass
    (mu : P → ℝ) (source : Fin M → P)
    (sigma : Equiv.Perm (Fin M)) (stores : Finset (Fin M)) :
    Green64PhysicalEdge.primeProduct mu
      (storedSourceList M source sigma stores) =
    ∏ i ∈ stores, mu (source (sigma i)) := by
  exact slots_primeProduct_eq M mu (fun i => source (sigma i)) stores

/-- Physical BIG source-active µ^M is balanced exactly by the
swapped FRESH integrations under edge reversal:
shared/source-store/source-drop versus shared/target-promote/target-fresh.
The source shared pattern is the ONLY equality assumption on labels;
duplicates in unshared slots are allowed (global distinct-birth later). -/
theorem physical_active_forward_reverse_mass
    (mu : P → ℝ) (source target : Fin M → P)
    (shared : Finset (Fin M))
    (sigma tau : Equiv.Perm (Fin M))
    (stores promote : Finset (Fin M))
    (hshared : ∀ j ∈ shared, source j = target j)
    (hs : stores ⊆ unsharedSource M shared sigma)
    (hp : promote ⊆ unsharedTarget M shared tau) :
    activeMass M mu source *
      freshIntegration M mu target shared tau promote *
      Green64PhysicalEdge.primeProduct mu
        (promotedTargetList M target tau promote) =
    activeMass M mu target *
      droppedSourceMass M mu source shared sigma stores *
      Green64PhysicalEdge.primeProduct mu
        (storedSourceList M source sigma stores) := by
  rw [activeMass_store_drop M mu source shared sigma stores hs,
      activeMass_promote_fresh M mu target shared tau promote hp,
      promotedTargetList_mass, storedSourceList_mass]
  unfold droppedSourceMass
  rw [shared_active_mass_eq M mu source target shared hshared]
  ring

end Green64FullPhysicalE

end

/-! ## PhysicalActiveFockJointMeasure -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p, NeZero (modulus p)]
variable (M : ℕ)

/-- The actual OLD-index injection multiplicity divided by its
Fock sector weight 1/(k+a)!, with NO extra factorial in E_i. -/
noncomputable def indexedFockFactor (k a : ℕ) : ℝ :=
  (((Nat.choose (k+a) a * Nat.factorial a : ℕ) : ℝ) /
    (Nat.factorial (k+a) : ℝ))

theorem indexedFockFactor_eq (k a : ℕ) :
    indexedFockFactor k a =
      1 / (Nat.factorial k : ℝ) :=
  Green64PhysicalEdge.source_input_injection_coefficient k a

/-- The forward source joint integral has true active µ^M, OLD
memory λ^j/j!, all independent target fresh integrations and
the ordered OLD-index promotion multiplicity. -/
noncomputable def forwardActiveFockCore
    (mu : P → ℝ) (step : ℤ)
    (u : List (Green64Fock.Atom P modulus))
    (source target : Fin M → P)
    (shared : Finset (Fin M))
    (sigma tau : Equiv.Perm (Fin M))
    (stores promote : Finset (Fin M)) : ℝ :=
  activeMass M mu source *
    Green64PhysicalEdge.atomProduct mu
      (Green64PhysicalEdge.sourceJointInput step u
        (promotedTargetList M target tau promote)) *
    indexedFockFactor u.length (promotedTargetList M target tau promote).length *
    freshIntegration M mu target shared tau promote

/-- In the reversed source physical edge, the active endpoint is
target, the OLD memory is Y, and the fresh draws are the original
DROPPED source slots. Fock sector has k+b positions. -/
noncomputable def reverseActiveFockCore
    (mu : P → ℝ) (step : ℤ)
    (u : List (Green64Fock.Atom P modulus))
    (source target : Fin M → P)
    (shared : Finset (Fin M))
    (sigma tau : Equiv.Perm (Fin M))
    (stores promote : Finset (Fin M)) : ℝ :=
  activeMass M mu target *
    Green64PhysicalEdge.atomProduct mu
      (Green64PhysicalEdge.sourceJointOutput step u
        (storedSourceList M source sigma stores)) *
    indexedFockFactor u.length (storedSourceList M source sigma stores).length *
    droppedSourceMass M mu source shared sigma stores

/-- Full physical BIG ACTIVE mu_tilde^M × Fock λ^j/j!
joint measure equality, BEFORE the asymmetric V_g^-a transfer
factors, at a fixed valid shared pattern and two endpoint
permutations. Arbitrary a,b, arbitrary identical atoms permitted.
Not merely a theorem for a reduced finite combinatorial proxy. -/
theorem physical_active_Fock_joint_measure_exact
    (mu : P → ℝ) (step : ℤ)
    (u : List (Green64Fock.Atom P modulus))
    (source target : Fin M → P)
    (shared : Finset (Fin M))
    (sigma tau : Equiv.Perm (Fin M))
    (stores promote : Finset (Fin M))
    (hshared : ∀ j ∈ shared, source j = target j)
    (hs : stores ⊆ unsharedSource M shared sigma)
    (hp : promote ⊆ unsharedTarget M shared tau) :
    forwardActiveFockCore modulus M mu step u source target
      shared sigma tau stores promote =
    reverseActiveFockCore modulus M mu step u source target
      shared sigma tau stores promote := by
  unfold forwardActiveFockCore reverseActiveFockCore
  rw [Green64PhysicalEdge.sourceJointInput_mass,
      Green64PhysicalEdge.sourceJointOutput_mass,
      indexedFockFactor_eq,indexedFockFactor_eq]
  have hactive := physical_active_forward_reverse_mass
    M mu source target shared sigma tau stores promote hshared hs hp

  let p := promotedTargetList M target tau promote
  let s := storedSourceList M source sigma stores
  let common := Green64PhysicalEdge.atomProduct mu u /
    (Nat.factorial u.length : ℝ)
  calc
    activeMass M mu source *
      (Green64PhysicalEdge.atomProduct mu u *
         Green64PhysicalEdge.primeProduct mu p) *
      (1 / (Nat.factorial u.length : ℝ)) *
      freshIntegration M mu target shared tau promote =
      (activeMass M mu source *
        freshIntegration M mu target shared tau promote *
        Green64PhysicalEdge.primeProduct mu p) * common := by
          dsimp [p,common]; ring
    _ = (activeMass M mu target *
      droppedSourceMass M mu source shared sigma stores *
      Green64PhysicalEdge.primeProduct mu s) * common := by
        dsimp [p,s]
        rw [hactive]
    _ = activeMass M mu target *
      (Green64PhysicalEdge.atomProduct mu u *
        Green64PhysicalEdge.primeProduct mu s) *
      (1 / (Nat.factorial u.length : ℝ)) *
      droppedSourceMass M mu source shared sigma stores := by
        dsimp [s,common]; ring

/-- Complete physical fixed-joint coefficient including the two
source rho endpoint factors and V_g^-a promotions. No j! appears
except in the single source Fock Hilbert weight. -/
noncomputable def forwardActiveFockJoint
    (mu : P → ℝ) (V rho : ℝ) (step : ℤ)
    (u : List (Green64Fock.Atom P modulus))
    (source target : Fin M → P)
    (shared : Finset (Fin M))
    (sigma tau : Equiv.Perm (Fin M))
    (stores promote : Finset (Fin M)) : ℝ :=
  forwardActiveFockCore modulus M mu step u source target
    shared sigma tau stores promote *
  Green64PhysicalEdge.jointRhoFactor rho step u
    (promotedTargetList M target tau promote)
    (storedSourceList M source sigma stores) /
  V ^ promote.card

noncomputable def reverseActiveFockJoint
    (mu : P → ℝ) (V rho : ℝ) (step : ℤ)
    (u : List (Green64Fock.Atom P modulus))
    (source target : Fin M → P)
    (shared : Finset (Fin M))
    (sigma tau : Equiv.Perm (Fin M))
    (stores promote : Finset (Fin M)) : ℝ :=
  reverseActiveFockCore modulus M mu step u source target
    shared sigma tau stores promote *
  Green64PhysicalEdge.jointRhoFactor rho step u
    (promotedTargetList M target tau promote)
    (storedSourceList M source sigma stores) /
  V ^ stores.card

/-- EXACT BIG ACTIVE+FOCK SOURCE E_i joint reversal ratio.
Its reverse orientation charges V^-b for the old stores,
the forward orientation charges V^-a for old promotions.
Preserves all λ(p,r), active µ^M, rho and factorial normalization.
Still requires a global branch-reversal bijection to obtain
an unrestricted full physical E Hilbert adjoint. -/
theorem physical_active_Fock_joint_V_reversal
    (mu : P → ℝ) (V rho : ℝ) (hV : V ≠ 0) (step : ℤ)
    (u : List (Green64Fock.Atom P modulus))
    (source target : Fin M → P)
    (shared : Finset (Fin M))
    (sigma tau : Equiv.Perm (Fin M))
    (stores promote : Finset (Fin M))
    (hshared : ∀ j ∈ shared, source j = target j)
    (hs : stores ⊆ unsharedSource M shared sigma)
    (hp : promote ⊆ unsharedTarget M shared tau) :
    forwardActiveFockJoint modulus M mu V rho step u source target
      shared sigma tau stores promote * V ^ promote.card =
    reverseActiveFockJoint modulus M mu V rho step u source target
      shared sigma tau stores promote * V ^ stores.card := by
  unfold forwardActiveFockJoint reverseActiveFockJoint
  rw [div_mul_cancel₀ _ (pow_ne_zero _ hV),
      div_mul_cancel₀ _ (pow_ne_zero _ hV)]
  rw [physical_active_Fock_joint_measure_exact
    modulus M mu step u source target shared sigma tau stores promote
    hshared hs hp]

end Green64FullPhysicalE

end

/-! ## PhysicalBigGroupTensor -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {BG : Type} [Fintype BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (modulus : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (modulus g p)]
variable (M : ℕ) (cap : BG → ℕ)

/-- Every BIG group has its own active mu_g^M and Fock 1/j_g!
sector. No grouped cross-factorial is ever introduced. -/
abbrev BigGroupState :=
  (g : BG) → BigState (modulus g) M (cap g)

abbrev BigGroupPerm := (g : BG) → Equiv.Perm (Fin M)

abbrev BigGroupTarget :=
  (g : BG) → BigPhysicalOutput (modulus g) M

abbrev BigGroupBranch (x : BigGroupState BP modulus M cap) :=
  (g : BG) → BigPhysicalBranch (modulus g) M (cap g) (x g)

noncomputable instance (x : BigGroupState BP modulus M cap) :
    Fintype (BigGroupBranch BP modulus M cap x) := inferInstance

/-- Exact product BIG active × Fock Hilbert measure. -/
noncomputable def bigGroupStateMass
    (mu : (g : BG) → BP g → ℝ)
    (x : BigGroupState BP modulus M cap) : ℝ :=
  ∏ g : BG, bigStateMass (modulus g) M (cap g) (mu g) (x g)

theorem bigGroupStateMass_positive
    (mu : (g : BG) → BP g → ℝ)
    (hmu : ∀ g p, 0 < mu g p)
    (x : BigGroupState BP modulus M cap) :
    0 < bigGroupStateMass BP modulus M cap mu x := by
  unfold bigGroupStateMass
  apply Finset.prod_pos
  intro g hg
  exact bigStateMass_positive (modulus g) M (cap g)
    (mu g) (hmu g) (x g)

/-- The independently sampled BIG-group choices all use the SAME
physical signed step Delta and divisor D, but each group has its
own ordered source/target permutations and stores/promotions. -/
def BigGroupEdgeLegal
    (x : BigGroupState BP modulus M cap)
    (shared : (g : BG) → Finset (Fin M))
    (sigma tau : BigGroupPerm (BG := BG) M)
    (D : ℕ) (step : ℤ)
    (branch : BigGroupBranch BP modulus M cap x) : Prop :=
  ∀ g : BG,
    PhysicalEdgeLegal (modulus g) M (cap g)
      (x g) (branch g).1 (shared g)
      (sigma g) (tau g) D step (branch g).2

noncomputable def legalBigGroupBranches
    (x : BigGroupState BP modulus M cap)
    (shared : (g : BG) → Finset (Fin M))
    (sigma tau : BigGroupPerm (BG := BG) M)
    (D : ℕ) (step : ℤ) :
    Finset (BigGroupBranch BP modulus M cap x) :=
  Finset.univ.filter
    (BigGroupEdgeLegal BP modulus M cap x shared sigma tau D step)

/-- Actual big group target active/memory multiset state for
the product of all independently selected source choices. -/
noncomputable def bigGroupBranchOutput
    (x : BigGroupState BP modulus M cap)
    (sigma : BigGroupPerm (BG := BG) M) (step : ℤ)
    (branch : BigGroupBranch BP modulus M cap x) :
    BigGroupTarget BP modulus M :=
  fun g => physicalBranchOutput (modulus g) M (cap g)
      (x g) (sigma g) step (branch g)

/-- Per-group BIG transfer rho^zeros V^-a mu_tilde^fresh,
with all OLD-index choice multiplicities retained.
A GLOBAL complex K is *not* inserted into this product. -/
noncomputable def bigGroupBranchWeight
    (mu : (g : BG) → BP g → ℝ)
    (V : BG → ℝ) (rho : ℝ)
    (x : BigGroupState BP modulus M cap)
    (shared : (g : BG) → Finset (Fin M))
    (sigma tau : BigGroupPerm (BG := BG) M)
    (step : ℤ)
    (branch : BigGroupBranch BP modulus M cap x) : ℂ :=
  ∏ g : BG, physicalBigBranchCoefficient (modulus g) M (cap g)
    (mu g) (V g) rho (x g) (branch g).1
    (shared g) (sigma g) (tau g) step (branch g).2

/-- Fixed-D all-big-group physical E_i finite operator row,
with every actual big ACTIVE fresh draw summed and every
indexed OLD promotion injection counted (no deduplication). -/
noncomputable def bigGroupFixedFrameRow
    (mu : (g : BG) → BP g → ℝ)
    (V : BG → ℝ) (rho : ℝ)
    (x : BigGroupState BP modulus M cap)
    (shared : (g : BG) → Finset (Fin M))
    (sigma tau : BigGroupPerm (BG := BG) M)
    (D : ℕ) (step : ℤ)
    (F : BigGroupTarget BP modulus M → ℂ) : ℂ :=
  ∑ branch ∈ legalBigGroupBranches BP modulus M cap x shared sigma tau D step,
    bigGroupBranchWeight BP modulus M cap mu V rho x shared
      sigma tau step branch *
      F (bigGroupBranchOutput BP modulus M cap x sigma step branch)

/-- Explicit original source groupwise Hilbert active×Fock measure
has exactly ONE j_g! per group (the coefficient remains in the
Hilbert mass, not multiplied again into a local E_i row). -/
theorem bigGroupMass_organized
    (mu : (g : BG) → BP g → ℝ)
    (x : BigGroupState BP modulus M cap) :
    bigGroupStateMass BP modulus M cap mu x =
      ∏ g : BG,
        (∏ i : Fin M, mu g ((x g).1 i)) *
          (Green64Fock.fockMass
            (Green64Fock.sourceAtomMu (mu g)) (x g).2) := by
  rfl

end Green64FullPhysicalE

end

/-! ## PhysicalBigGroupJointMeasure -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {BG : Type} [Fintype BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (modulus : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (modulus g p)]
variable (M : ℕ)

/-- All source physical intermediate BIG Fock survivor lists at the
fixed joint E_i edge, with own ZMod p labels in each group. -/
abbrev GroupJointSurvivors :=
  (g : BG) → List (Green64Fock.Atom (BP g) (modulus g))

abbrev GroupActiveSlots := (g : BG) → Fin M → BP g
abbrev GroupIndexSets := (g : BG) → Finset (Fin M)

/-- Actual all-group source ACTIVE mu^M, Fock λ^j/j!,
OLD index multiplicities, rho endpoint factors and V^-a. -/
noncomputable def fullBigJointForward
    (mu : (g : BG) → BP g → ℝ) (V : BG → ℝ)
    (rho : ℝ) (step : ℤ)
    (u : GroupJointSurvivors BP modulus)
    (source target : GroupActiveSlots BP M)
    (shared stores promote : GroupIndexSets (BG := BG) M)
    (sigma tau : BigGroupPerm (BG := BG) M) : ℝ :=
  ∏ g : BG,
    forwardActiveFockJoint (modulus g) M (mu g) (V g) rho step
      (u g) (source g) (target g) (shared g)
      (sigma g) (tau g) (stores g) (promote g)

noncomputable def fullBigJointReverse
    (mu : (g : BG) → BP g → ℝ) (V : BG → ℝ)
    (rho : ℝ) (step : ℤ)
    (u : GroupJointSurvivors BP modulus)
    (source target : GroupActiveSlots BP M)
    (shared stores promote : GroupIndexSets (BG := BG) M)
    (sigma tau : BigGroupPerm (BG := BG) M) : ℝ :=
  ∏ g : BG,
    reverseActiveFockJoint (modulus g) M (mu g) (V g) rho step
      (u g) (source g) (target g) (shared g)
      (sigma g) (tau g) (stores g) (promote g)

/-- For ALL BIG source groups, including empty collections and
repeated Fock atoms, exact physical source E joint forward/reverse
V ratio follows from the real groupwise measure, WITHOUT a
spurious cross-group factorial, zero-residue /p or extra K. -/
theorem fullBigJoint_exact_reversal
    (mu : (g : BG) → BP g → ℝ) (V : BG → ℝ)
    (hV : ∀ g, V g ≠ 0)
    (rho : ℝ) (step : ℤ)
    (u : GroupJointSurvivors BP modulus)
    (source target : GroupActiveSlots BP M)
    (shared stores promote : GroupIndexSets (BG := BG) M)
    (sigma tau : BigGroupPerm (BG := BG) M)
    (hshared : ∀ g j, j ∈ shared g → source g j = target g j)
    (hs : ∀ g, stores g ⊆ unsharedSource M (shared g) (sigma g))
    (hp : ∀ g, promote g ⊆ unsharedTarget M (shared g) (tau g)) :
    fullBigJointForward BP modulus M mu V rho step u source target
      shared stores promote sigma tau *
      (∏ g : BG, V g ^ (promote g).card) =
    fullBigJointReverse BP modulus M mu V rho step u source target
      shared stores promote sigma tau *
      (∏ g : BG, V g ^ (stores g).card) := by
  unfold fullBigJointForward fullBigJointReverse
  rw [← Finset.prod_mul_distrib,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro g hg
  exact physical_active_Fock_joint_V_reversal
    (modulus g) M (mu g) (V g) rho (hV g) step
    (u g) (source g) (target g) (shared g)
    (sigma g) (tau g) (stores g) (promote g)
    (hshared g) (hs g) (hp g)

end Green64FullPhysicalE

end

/-! ## ChronologicalSeenBirthEquiv -/

section

open scoped BigOperators Classical
noncomputable section

namespace Green64Analytic.CorrelationSquare

set_option autoImplicit false

/-- Legal chronological source states: the new numerical births are disjoint
from the complete set of numerical primes seen before the row. -/
abbrev SourceChronologicalSeenBirth434 (ι : Type) [DecidableEq ι] :=
  {p : Finset ι × Finset ι // Disjoint p.1 p.2}

/-- The same row indexed at its target: the birth set is retained as an AUX
coordinate and is contained in the updated seen set.  Retaining it is exactly
what makes the chronological update invertible. -/
abbrev TargetChronologicalSeenBirth434 (ι : Type) [DecidableEq ι] :=
  {p : Finset ι × Finset ι // p.2 ⊆ p.1}

/-- Exact chronological change of variables

    `(seen, births) ↦ (seen ∪ births, births)`.

The inverse is `(updated, births) ↦ (updated \ births, births)`.  Thus the
history coordinate is transported, rather than discarded or bounded by the
number of possible seen sets. -/
def sourceChronologicalSeenBirthEquiv434
    (ι : Type) [DecidableEq ι] :
    SourceChronologicalSeenBirth434 ι ≃
      TargetChronologicalSeenBirth434 ι where
  toFun p := ⟨(p.1.1 ∪ p.1.2, p.1.2), by
    intro x hx
    exact Finset.mem_union_right _ hx⟩
  invFun q := ⟨(q.1.1 \ q.1.2, q.1.2), by
    rw [Finset.disjoint_left]
    intro x hxDiff hxBirth
    exact (Finset.mem_sdiff.mp hxDiff).2 hxBirth⟩
  left_inv p := by
    rcases p with ⟨⟨S, B⟩, hSB⟩
    apply Subtype.ext
    apply Prod.ext
    · ext x
      simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · rintro ⟨hxS | hxB, hnotB⟩
        · exact hxS
        · exact (hnotB hxB).elim
      · intro hxS
        exact ⟨Or.inl hxS, fun hxB =>
          (Finset.disjoint_left.mp hSB hxS hxB).elim⟩
    · rfl
  right_inv q := by
    rcases q with ⟨⟨T, B⟩, hBT⟩
    apply Subtype.ext
    apply Prod.ext
    · ext x
      simp only [Finset.mem_union, Finset.mem_sdiff]
      constructor
      · rintro (⟨hxT, _⟩ | hxB)
        · exact hxT
        · exact hBT hxB
      · intro hxT
        by_cases hxB : x ∈ B
        · exact Or.inr hxB
        · exact Or.inl ⟨hxT, hxB⟩
    · rfl

/-- The target seen set is literally the original seen set union the births;
this is the consumer equality needed by the marked physical future. -/
theorem source_chronological_seen_birth_target434
    (ι : Type) [DecidableEq ι]
    (p : SourceChronologicalSeenBirth434 ι) :
    (sourceChronologicalSeenBirthEquiv434 ι p).1.1 = p.1.1 ∪ p.1.2 := by
  rfl

/-- Recovery of the complete predecessor seen state.  No global cardinality
cap and no summation over predecessor histories occurs. -/
theorem source_chronological_seen_birth_recover434
    (ι : Type) [DecidableEq ι]
    (p : SourceChronologicalSeenBirth434 ι) :
    (sourceChronologicalSeenBirthEquiv434 ι p).1.1 \
        (sourceChronologicalSeenBirthEquiv434 ι p).1.2 = p.1.1 := by
  rcases p with ⟨⟨S, B⟩, hSB⟩
  change (S ∪ B) \ B = S
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_union]
  constructor
  · rintro ⟨hxS | hxB, hnotB⟩
    · exact hxS
    · exact (hnotB hxB).elim
  · intro hxS
    exact ⟨Or.inl hxS, fun hxB =>
      (Finset.disjoint_left.mp hSB hxS hxB).elim⟩

/-- Finite weighted sums push forward exactly through the chronological
change of variables.  In particular, applying this with a squared norm as
`W` introduces no history-count, Fock-sector, OLD-mode, Fourier-mode or
global-xi factor. -/
theorem source_chronological_seen_birth_finset_pushforward434
    (ι M : Type) [DecidableEq ι] [AddCommMonoid M]
    (A : Finset (SourceChronologicalSeenBirth434 ι))
    (W : TargetChronologicalSeenBirth434 ι → M) :
    (A.map (sourceChronologicalSeenBirthEquiv434 ι).toEmbedding).sum W =
      A.sum (fun p => W (sourceChronologicalSeenBirthEquiv434 ι p)) := by
  simpa using
    (Finset.sum_map (sourceChronologicalSeenBirthEquiv434 ι).toEmbedding A W)

/-- The exact L² direct-sum version of the same pushforward. -/
theorem source_chronological_seen_birth_L2_pushforward434
    (ι : Type) [DecidableEq ι]
    (A : Finset (SourceChronologicalSeenBirth434 ι))
    (F : TargetChronologicalSeenBirth434 ι → ℂ) :
    (A.map (sourceChronologicalSeenBirthEquiv434 ι).toEmbedding).sum
        (fun q => ‖F q‖ ^ 2) =
      A.sum (fun p => ‖F (sourceChronologicalSeenBirthEquiv434 ι p)‖ ^ 2) := by
  simpa using
    (Finset.sum_map (sourceChronologicalSeenBirthEquiv434 ι).toEmbedding A
      (fun q => ‖F q‖ ^ 2))

end Green64Analytic.CorrelationSquare

end

end

/-! ## ChronologicalPhysicalDirectSum -/

section

open scoped BigOperators Classical
noncomputable section

namespace Green64Analytic.CorrelationSquare

set_option autoImplicit false

/-- The physical endpoint is carried unchanged while the numerical history is
reindexed from predecessor seen state to updated seen state. -/
def sourceChronologicalPhysicalEquiv434
    (Out ι : Type) [DecidableEq ι] :
    (Out × SourceChronologicalSeenBirth434 ι) ≃
      (Out × TargetChronologicalSeenBirth434 ι) :=
  Equiv.prodCongr (Equiv.refl Out) (sourceChronologicalSeenBirthEquiv434 ι)

/-- A chronological future is evaluated on the genuine physical output and
the updated seen set stored in the target carrier. -/
def sourceChronologicalTargetFuture434
    (Out ι : Type) [DecidableEq ι]
    (F : Out → Finset ι → ℂ)
    (q : Out × TargetChronologicalSeenBirth434 ι) : ℂ :=
  F q.1 q.2.1.1

/-- Exact consumer identity for the literal marked-row future. -/
theorem source_chronological_physical_future_target434
    (Out ι : Type) [DecidableEq ι]
    (F : Out → Finset ι → ℂ)
    (p : Out × SourceChronologicalSeenBirth434 ι) :
    sourceChronologicalTargetFuture434 Out ι F
        (sourceChronologicalPhysicalEquiv434 Out ι p) =
      F p.1 (p.2.1.1 ∪ p.2.1.2) := by
  rfl

/-- Exact weighted direct-sum reindexing on the augmented physical carrier. -/
theorem source_chronological_physical_finset_pushforward434
    (Out ι M : Type) [DecidableEq Out] [DecidableEq ι] [AddCommMonoid M]
    (A : Finset (Out × SourceChronologicalSeenBirth434 ι))
    (W : Out × TargetChronologicalSeenBirth434 ι → M) :
    (A.map (sourceChronologicalPhysicalEquiv434 Out ι).toEmbedding).sum W =
      A.sum (fun p => W (sourceChronologicalPhysicalEquiv434 Out ι p)) := by
  simpa using
    (Finset.sum_map (sourceChronologicalPhysicalEquiv434 Out ι).toEmbedding A W)

/-- Exact physical L² pushforward.  The equality is before any triangle or
Cauchy--Schwarz step, so no cardinality factor can be introduced here. -/
theorem source_chronological_physical_L2_pushforward434
    (Out ι : Type) [DecidableEq Out] [DecidableEq ι]
    (A : Finset (Out × SourceChronologicalSeenBirth434 ι))
    (F : Out → Finset ι → ℂ) :
    (A.map (sourceChronologicalPhysicalEquiv434 Out ι).toEmbedding).sum
      (fun q => ‖sourceChronologicalTargetFuture434 Out ι F q‖ ^ 2) =
      A.sum (fun p => ‖F p.1 (p.2.1.1 ∪ p.2.1.2)‖ ^ 2) := by
  rw [source_chronological_physical_finset_pushforward434]
  apply Finset.sum_congr rfl
  intro p hp
  rw [source_chronological_physical_future_target434]

end Green64Analytic.CorrelationSquare

end

end

