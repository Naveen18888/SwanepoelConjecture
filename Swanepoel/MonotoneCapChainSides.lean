module
public import Swanepoel.MonotoneCapChain
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

theorem PennyGraph.cap_strip_contact_cannot_cross {n : ℕ} (G : PennyGraph n)
    (l : Plane →ₗ[ℝ] ℝ) (a b : Fin n) (hab : G.graph.Adj a b)
    (hpositive : 0 < l (G.point b-G.point a)) (c d : Fin n) (hcd : G.graph.Adj c d)
    (hca : c ≠ a) (hcb : c ≠ b)
    (hc0 : 0 ≤ l (G.point c-G.point a)) (hc1 : l (G.point c-G.point a) ≤ l (G.point b-G.point a))
    (hd0 : 0 ≤ l (G.point d-G.point a)) (hd1 : l (G.point d-G.point a) ≤ l (G.point b-G.point a))
    (hc : 0 < cross2 (G.point b-G.point a) (G.point c-G.point a))
    (hd : cross2 (G.point b-G.point a) (G.point d-G.point a) < 0) : False := by
  let v := G.point b-G.point a
  let C := cross2 v (G.point c-G.point a)
  let D := cross2 v (G.point d-G.point a)
  let t := C/(C-D)
  let z := G.edgePoint c d t
  have hden : 0 < C-D := by dsimp [C,D,v]; linarith
  have ht0 : 0 < t := div_pos hc hden
  have ht1 : t < 1 := by apply (div_lt_iff₀ hden).mpr; dsimp [C,D,v]; linarith
  have htden : t*(C-D) = C := div_mul_cancel₀ _ hden.ne'
  have hzsplit : z-G.point a =
      (1-t) • (G.point c-G.point a)+t • (G.point d-G.point a) := by
    dsimp [z,PennyGraph.edgePoint]
    module
  have hzcross : cross2 v (z-G.point a) = 0 := by
    rw [hzsplit,cross2_add_right,cross2_smul_right,cross2_smul_right]
    change (1-t)*C+t*D = 0
    nlinarith
  have hlz : l (z-G.point a) = (1-t)*l (G.point c-G.point a)+t*l (G.point d-G.point a) := by
    rw [hzsplit,map_add,map_smul,map_smul,smul_eq_mul,smul_eq_mul]
  have hz0 : 0 ≤ l (z-G.point a) := by
    rw [hlz]
    exact add_nonneg (mul_nonneg (by linarith) hc0) (mul_nonneg ht0.le hd0)
  have hz1 : l (z-G.point a) ≤ l (G.point b-G.point a) := by
    have h1 := mul_le_mul_of_nonneg_left hc1 (by linarith : 0 ≤ 1-t)
    have h2 := mul_le_mul_of_nonneg_left hd1 ht0.le
    rw [hlz]
    nlinarith
  obtain ⟨s,⟨hs0,hs1⟩,hs⟩ := G.cap_strip_cross_zero_mem_trace l a b hab hpositive z hz0 hz1 hzcross
  have heq : G.edgePoint c d t = G.edgePoint a b s := hs.symm
  have hsame := G.interior_edge_intersection c d a b hcd hab ht0 ht1 hs0 hs1 heq
  rcases Sym2.eq_iff.mp hsame with h | h
  · exact hca h.1
  · exact hcb h.1

theorem PennyGraph.cap_strip_contact_same_side {n : ℕ} (G : PennyGraph n)
    (l : Plane →ₗ[ℝ] ℝ) (a b : Fin n) (hab : G.graph.Adj a b)
    (hpositive : 0 < l (G.point b-G.point a)) (c d : Fin n) (hcd : G.graph.Adj c d)
    (hca : c ≠ a) (hcb : c ≠ b) (hda : d ≠ a) (hdb : d ≠ b)
    (hc0 : 0 ≤ l (G.point c-G.point a)) (hc1 : l (G.point c-G.point a) ≤ l (G.point b-G.point a))
    (hd0 : 0 ≤ l (G.point d-G.point a)) (hd1 : l (G.point d-G.point a) ≤ l (G.point b-G.point a)) :
    (0 < cross2 (G.point b-G.point a) (G.point c-G.point a) ∧
      0 < cross2 (G.point b-G.point a) (G.point d-G.point a)) ∨
    (cross2 (G.point b-G.point a) (G.point c-G.point a) < 0 ∧
      cross2 (G.point b-G.point a) (G.point d-G.point a) < 0) := by
  have hcne : cross2 (G.point b-G.point a) (G.point c-G.point a) ≠ 0 := by
    intro h
    rcases G.cap_strip_collinear_vertex_eq_endpoint l a b hab hpositive c hc0 hc1 h with h | h
    · exact hca h
    · exact hcb h
  have hdne : cross2 (G.point b-G.point a) (G.point d-G.point a) ≠ 0 := by
    intro h
    rcases G.cap_strip_collinear_vertex_eq_endpoint l a b hab hpositive d hd0 hd1 h with h | h
    · exact hda h
    · exact hdb h
  by_cases hc : 0 < cross2 (G.point b-G.point a) (G.point c-G.point a)
  · left
    refine ⟨hc,?_⟩
    by_contra hn
    have hd : cross2 (G.point b-G.point a) (G.point d-G.point a) < 0 :=
      lt_of_le_of_ne (le_of_not_gt hn) hdne
    exact G.cap_strip_contact_cannot_cross l a b hab hpositive c d hcd hca hcb hc0 hc1 hd0 hd1 hc hd
  · right
    have hcneg : cross2 (G.point b-G.point a) (G.point c-G.point a) < 0 :=
      lt_of_le_of_ne (le_of_not_gt hc) hcne
    refine ⟨hcneg,?_⟩
    by_contra hn
    have hd : 0 < cross2 (G.point b-G.point a) (G.point d-G.point a) :=
      lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hdne)
    exact G.cap_strip_contact_cannot_cross l a b hab hpositive d c hcd.symm hda hdb hd0 hd1 hc0 hc1 hd hcneg

theorem PennyGraph.monotone_cap_chain_same_side {n k : ℕ} (G : PennyGraph n)
    (l : Plane →ₗ[ℝ] ℝ) (p : ℕ → Fin n) (hk : 2 ≤ k)
    (hcap : G.graph.Adj (p 0) (p k)) (hpositive : 0 < l (G.point (p k)-G.point (p 0)))
    (hcontact : ∀ i, i < k → G.graph.Adj (p i) (p (i+1)))
    (hback : ∀ i, i+2 ≤ k → p i ≠ p (i+2))
    (hmono : Monotone (fun i : ℕ => l (G.point (p i)))) :
    (0 < cross2 (G.point (p k)-G.point (p 0)) (G.point (p 1)-G.point (p 0)) ∧
      0 < cross2 (G.point (p k)-G.point (p 0)) (G.point (p (k-1))-G.point (p k))) ∨
    (cross2 (G.point (p k)-G.point (p 0)) (G.point (p 1)-G.point (p 0)) < 0 ∧
      cross2 (G.point (p k)-G.point (p 0)) (G.point (p (k-1))-G.point (p k)) < 0) := by
  let v := G.point (p k)-G.point (p 0)
  let H (i : ℕ) := cross2 v (G.point (p i)-G.point (p 0))
  have hinj := G.monotone_chain_index_injective l v hpositive.ne' p hcontact hback hmono
  have hnotA (i : ℕ) (hi : 0 < i) (hik : i < k) : p i ≠ p 0 := by
    intro he
    have hh := hinj i hik.le 0 (by omega) he
    omega
  have hnotB (i : ℕ) (hi : 0 < i) (hik : i < k) : p i ≠ p k := by
    intro he
    have hh := hinj i hik.le k le_rfl he
    omega
  have hstrip (i : ℕ) (hi : i ≤ k) : 0 ≤ l (G.point (p i)-G.point (p 0)) ∧
      l (G.point (p i)-G.point (p 0)) ≤ l v := by
    have h0 := hmono (Nat.zero_le i)
    have h1 := hmono hi
    dsimp [v]
    rw [map_sub,map_sub]
    constructor <;> linarith
  have hne (i : ℕ) (hi : 0 < i) (hik : i < k) : H i ≠ 0 := by
    intro hz
    rcases G.cap_strip_collinear_vertex_eq_endpoint l (p 0) (p k) hcap hpositive (p i)
      (hstrip i hik.le).1 (hstrip i hik.le).2 hz with h | h
    · exact hnotA i hi hik h
    · exact hnotB i hi hik h
  have hstep (i : ℕ) (hi : 1 ≤ i) (hik : i+1 < k) : (0 < H i) ↔ 0 < H (i+1) := by
    have hs := G.cap_strip_contact_same_side l (p 0) (p k) hcap hpositive
      (p i) (p (i+1)) (hcontact i (by omega))
      (hnotA i (by omega) (by omega)) (hnotB i (by omega) (by omega))
      (hnotA (i+1) (by omega) hik) (hnotB (i+1) (by omega) hik)
      (hstrip i (by omega)).1 (hstrip i (by omega)).2
      (hstrip (i+1) hik.le).1 (hstrip (i+1) hik.le).2
    rcases hs with ⟨h1,h2⟩ | ⟨h1,h2⟩
    · exact iff_of_true h1 h2
    · exact iff_of_false (not_lt_of_ge h1.le) (not_lt_of_ge h2.le)
  have hall : ∀ i, 1 ≤ i → i < k → ((0 < H i) ↔ 0 < H 1) := by
    intro i
    induction i with
    | zero => intro hi; omega
    | succ i ih =>
      intro hi hik
      by_cases hiz : i = 0
      · subst i; rfl
      · exact (hstep i (by omega) hik).symm.trans (ih (by omega) (by omega))
  have hlast : cross2 v (G.point (p (k-1))-G.point (p k)) = H (k-1) := by
    have he : G.point (p (k-1))-G.point (p k) = (G.point (p (k-1))-G.point (p 0))-v := by
      dsimp [v]
      abel
    rw [he,cross2_sub_right,cross2_self,sub_zero]
  change (0 < H 1 ∧ 0 < cross2 v (G.point (p (k-1))-G.point (p k))) ∨
    (H 1 < 0 ∧ cross2 v (G.point (p (k-1))-G.point (p k)) < 0)
  rw [hlast]
  by_cases hfirst : 0 < H 1
  · exact Or.inl ⟨hfirst,(hall (k-1) (by omega) (by omega)).mpr hfirst⟩
  · right
    refine ⟨lt_of_le_of_ne (le_of_not_gt hfirst) (hne 1 (by omega) (by omega)),?_⟩
    apply lt_of_le_of_ne ?_ (hne (k-1) (by omega) (by omega))
    exact le_of_not_gt (fun h => hfirst ((hall (k-1) (by omega) (by omega)).mp h))

theorem PennyGraph.monotone_cap_chain_cross_ratio {n k : ℕ} (G : PennyGraph n)
    (l : Plane →ₗ[ℝ] ℝ) (p : ℕ → Fin n) (hk : 2 ≤ k)
    (hcap : G.graph.Adj (p 0) (p k)) (hpositive : 0 < l (G.point (p k)-G.point (p 0)))
    (hcontact : ∀ i, i < k → G.graph.Adj (p i) (p (i+1)))
    (hback : ∀ i, i+2 ≤ k → p i ≠ p (i+2))
    (hmono : Monotone (fun i : ℕ => l (G.point (p i)))) :
    cross2 (G.point (p k)-G.point (p 0)) (G.point (p (k-1))-G.point (p k)) ≠ 0 ∧
    0 < cross2 (G.point (p k)-G.point (p 0)) (G.point (p 1)-G.point (p 0)) /
      cross2 (G.point (p k)-G.point (p 0)) (G.point (p (k-1))-G.point (p k)) := by
  rcases G.monotone_cap_chain_same_side l p hk hcap hpositive hcontact hback hmono with
    ⟨h1,h2⟩ | ⟨h1,h2⟩
  · exact ⟨ne_of_gt h2,div_pos h1 h2⟩
  · exact ⟨ne_of_lt h2,div_pos_of_neg_of_neg h1 h2⟩

theorem PennyGraph.monotone_cap_walk_cross_ratio {n : ℕ} (G : PennyGraph n)
    (l : Plane →ₗ[ℝ] ℝ) {a b : Fin n} (q : G.graph.Walk a b) (hk : 2 ≤ q.length)
    (hcap : G.graph.Adj a b) (hpositive : 0 < l (G.point b-G.point a))
    (hprojection : ∀ i, i < q.length → 0 ≤ l (G.point (q.getVert (i+1))-G.point (q.getVert i)))
    (hback : ∀ i, i+2 ≤ q.length → q.getVert i ≠ q.getVert (i+2)) :
    cross2 (G.point b-G.point a) (G.point (q.getVert (q.length-1))-G.point b) ≠ 0 ∧
    0 < cross2 (G.point b-G.point a) (G.point (q.getVert 1)-G.point a) /
      cross2 (G.point b-G.point a) (G.point (q.getVert (q.length-1))-G.point b) := by
  have hc : G.graph.Adj (q.getVert 0) (q.getVert q.length) := by simpa using hcap
  have hp : 0 < l (G.point (q.getVert q.length)-G.point (q.getVert 0)) := by simpa using hpositive
  simpa only [q.getVert_zero,q.getVert_length] using
    G.monotone_cap_chain_cross_ratio l q.getVert hk hc hp
      (fun i hi => q.adj_getVert_succ hi) hback (G.walk_projection_monotone l q hprojection)

end Swanepoel
