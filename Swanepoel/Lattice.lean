module
public import Swanepoel.Definitions
@[expose] public section

noncomputable section
namespace Swanepoel

abbrev LatticeSite := ℕ × ℕ

def latticePoint (p : LatticeSite) : Plane :=
  WithLp.toLp 2 ![(p.1 : ℝ), (p.2 : ℝ)]

def LatticeAdj (p q : LatticeSite) : Prop :=
  (p.1+1=q.1 ∧ p.2=q.2) ∨ (q.1+1=p.1 ∧ q.2=p.2) ∨
  (p.1=q.1 ∧ p.2+1=q.2) ∨ (q.1=p.1 ∧ q.2+1=p.2)

theorem lattice_dist_sq (p q : LatticeSite) :
    dist (latticePoint p) (latticePoint q)^2 =
      ((p.1 : ℝ)-q.1)^2 + ((p.2 : ℝ)-q.2)^2 := by
  rw [dist_eq_norm, EuclideanSpace.real_norm_sq_eq]
  simp [latticePoint, Fin.sum_univ_two]

theorem int_sq_ge_one {x : ℤ} (hx : x ≠ 0) : 1 ≤ x^2 := by
  have h := sq_pos_of_ne_zero hx
  omega

theorem lattice_separated (p q : LatticeSite) (hne : p ≠ q) :
    1 ≤ dist (latticePoint p) (latticePoint q) := by
  have hcoords : p.1 ≠ q.1 ∨ p.2 ≠ q.2 := by
    by_contra h
    simp only [not_or, not_not] at h
    exact hne (Prod.ext h.1 h.2)
  have hsq : (1 : ℝ) ≤ ((p.1 : ℝ)-q.1)^2 + ((p.2 : ℝ)-q.2)^2 := by
    rcases hcoords with h | h
    · have hi : (p.1 : ℤ)-q.1 ≠ 0 := by omega
      have hh : (1 : ℝ) ≤ ((p.1 : ℝ)-q.1)^2 := by exact_mod_cast int_sq_ge_one hi
      nlinarith [sq_nonneg ((p.2 : ℝ)-q.2)]
    · have hi : (p.2 : ℤ)-q.2 ≠ 0 := by omega
      have hh : (1 : ℝ) ≤ ((p.2 : ℝ)-q.2)^2 := by exact_mod_cast int_sq_ge_one hi
      nlinarith [sq_nonneg ((p.1 : ℝ)-q.1)]
  rw [← lattice_dist_sq] at hsq
  nlinarith [show 0 ≤ dist (latticePoint p) (latticePoint q) from dist_nonneg]

theorem lattice_contact (p q : LatticeSite) :
    dist (latticePoint p) (latticePoint q) = 1 ↔ LatticeAdj p q := by
  constructor
  · intro hd
    have hsq := lattice_dist_sq p q
    rw [hd] at hsq
    have hi : ((p.1 : ℤ)-q.1)^2 + ((p.2 : ℤ)-q.2)^2 = 1 := by
      exact_mod_cast hsq.symm
    have hz : (p.1 : ℤ)-q.1 = 0 ∨ (p.2 : ℤ)-q.2 = 0 := by
      by_contra h
      simp only [not_or] at h
      have hx := int_sq_ge_one h.1
      have hy := int_sq_ge_one h.2
      omega
    rcases hz with hx | hy
    · rw [hx] at hi
      have h : (p.2 : ℤ)-q.2 = 1 ∨ (p.2 : ℤ)-q.2 = -1 := by
        have he : ((p.2 : ℤ)-q.2)^2 = 1 := by nlinarith [hi]
        exact sq_eq_one_iff.mp he
      unfold LatticeAdj
      omega
    · rw [hy] at hi
      have h : (p.1 : ℤ)-q.1 = 1 ∨ (p.1 : ℤ)-q.1 = -1 := by
        have he : ((p.1 : ℤ)-q.1)^2 = 1 := by nlinarith [hi]
        exact sq_eq_one_iff.mp he
      unfold LatticeAdj
      omega
  · intro h
    have hsq := lattice_dist_sq p q
    have hxy : ((p.1 : ℝ)-q.1)^2 + ((p.2 : ℝ)-q.2)^2 = 1 := by
      rcases h with h | h | h | h
      · have h1 : (p.1 : ℝ)+1=q.1 := by exact_mod_cast h.1
        have h2 : (p.2 : ℝ)=q.2 := by exact_mod_cast h.2
        nlinarith
      · have h1 : (q.1 : ℝ)+1=p.1 := by exact_mod_cast h.1
        have h2 : (q.2 : ℝ)=p.2 := by exact_mod_cast h.2
        nlinarith
      · have h1 : (p.1 : ℝ)=q.1 := by exact_mod_cast h.1
        have h2 : (p.2 : ℝ)+1=q.2 := by exact_mod_cast h.2
        nlinarith
      · have h1 : (q.1 : ℝ)=p.1 := by exact_mod_cast h.1
        have h2 : (q.2 : ℝ)+1=p.2 := by exact_mod_cast h.2
        nlinarith
    rw [hxy] at hsq
    nlinarith [show 0 ≤ dist (latticePoint p) (latticePoint q) from dist_nonneg]

theorem lattice_parity (p q : LatticeSite) (hpq : LatticeAdj p q) :
    (p.1+p.2)%2 ≠ (q.1+q.2)%2 := by rcases hpq with h | h | h | h <;> omega

def latticeGraph (S : Finset LatticeSite) : SimpleGraph S where
  Adj p q := LatticeAdj p q
  symm := ⟨by intro p q h; unfold LatticeAdj at *; tauto⟩
  loopless := ⟨by intro p h; unfold LatticeAdj at h; omega⟩

def latticeConfiguration (S : Finset LatticeSite) {n : ℕ} (hn : S.card = n) : PennyGraph n where
  point i := latticePoint ((S.equivFinOfCardEq hn).symm i)
  separated i j hij := lattice_separated _ _ (by
    intro h
    exact hij ((S.equivFinOfCardEq hn).symm.injective (Subtype.ext h)))

theorem latticeConfiguration_triangleFree (S : Finset LatticeSite) {n : ℕ}
    (hn : S.card = n) : (latticeConfiguration S hn).TriangleFree := by
  intro a b c hab hbc hca
  have h1 := lattice_parity _ _ ((lattice_contact _ _).mp hab.2)
  have h2 := lattice_parity _ _ ((lattice_contact _ _).mp hbc.2)
  have h3 := lattice_parity _ _ ((lattice_contact _ _).mp hca.2)
  omega

end Swanepoel
