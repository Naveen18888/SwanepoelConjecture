module
public import Swanepoel.FaceBoundaryOrder
public import Mathlib.Combinatorics.SimpleGraph.Paths
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

theorem plane_linear_kernel_cross_zero (l : Plane →ₗ[ℝ] ℝ) (v : Plane) (hv : l v ≠ 0)
    {u w : Plane} (hu : l u = 0) (hw : l w = 0) : cross2 u w = 0 := by
  have hid : cross2 u w • v = cross2 v w • u+cross2 u v • w := by
    ext i
    fin_cases i <;> simp [cross2] <;> ring
  have hr := congrArg l hid
  simp only [map_smul,map_add,hu,hw,smul_eq_mul,mul_zero,add_zero] at hr
  exact (mul_eq_zero.mp hr).resolve_right hv

theorem PennyGraph.flat_two_step_vectors_eq {n : ℕ} (G : PennyGraph n)
    (l : Plane →ₗ[ℝ] ℝ) (v : Plane) (hv : l v ≠ 0)
    (a b c : Fin n) (hab : G.graph.Adj a b) (hbc : G.graph.Adj b c) (hac : a ≠ c)
    (hlab : l (G.point b) = l (G.point a)) (hlbc : l (G.point c) = l (G.point b)) :
    G.point c-G.point b = G.point b-G.point a := by
  have hu : ‖G.point b-G.point a‖ = 1 := by simpa only [← dist_eq_norm] using hab.symm.2
  have hw : ‖G.point c-G.point b‖ = 1 := by simpa only [← dist_eq_norm] using hbc.symm.2
  have hlu : l (G.point b-G.point a) = 0 := by rw [map_sub,hlab,sub_self]
  have hlw : l (G.point c-G.point b) = 0 := by rw [map_sub,hlbc,sub_self]
  have hcross := plane_linear_kernel_cross_zero l v hv hlu hlw
  rcases unit_cross_zero_eq_or_neg _ _ hu hw hcross with heq | hneg
  · exact heq
  · exfalso
    apply hac
    apply G.point_injective
    have hz : G.point c-G.point a = 0 := by
      calc
        _ = (G.point c-G.point b)+(G.point b-G.point a) := by abel
        _ = 0 := by rw [hneg]; abel
    exact (sub_eq_zero.mp hz).symm

theorem PennyGraph.flat_chain_displacement {n k : ℕ} (G : PennyGraph n)
    (l : Plane →ₗ[ℝ] ℝ) (v : Plane) (hv : l v ≠ 0) (p : ℕ → Fin n) (_hk : 0 < k)
    (hcontact : ∀ i, i < k → G.graph.Adj (p i) (p (i+1)))
    (hback : ∀ i, i+2 ≤ k → p i ≠ p (i+2))
    (hflat : ∀ i, i ≤ k → l (G.point (p i)) = l (G.point (p 0))) :
    G.point (p k) = G.point (p 0)+(k : ℝ) • (G.point (p 1)-G.point (p 0)) := by
  let u := G.point (p 1)-G.point (p 0)
  have hvector : ∀ i, i < k → G.point (p (i+1))-G.point (p i) = u := by
    intro i
    induction i with
    | zero => intro _; rfl
    | succ i ih =>
      intro hi
      have heq := G.flat_two_step_vectors_eq l v hv (p i) (p (i+1)) (p (i+2))
        (hcontact i (by omega)) (hcontact (i+1) (by omega)) (hback i (by omega))
        ((hflat (i+1) (by omega)).trans (hflat i (by omega)).symm)
        ((hflat (i+2) (by omega)).trans (hflat (i+1) (by omega)).symm)
      exact heq.trans (ih (by omega))
  have hpoint : ∀ i, i ≤ k → G.point (p i) = G.point (p 0)+(i : ℝ) • u := by
    intro i
    induction i with
    | zero => intro _; simp
    | succ i ih =>
      intro hi
      have hvec := hvector i (by omega)
      calc
        _ = G.point (p i)+u := by rw [← hvec]; abel
        _ = (G.point (p 0)+(i : ℝ) • u)+u := by rw [ih (by omega)]
        _ = _ := by push_cast; module
  exact hpoint k le_rfl

theorem PennyGraph.flat_chain_no_return {n k : ℕ} (G : PennyGraph n)
    (l : Plane →ₗ[ℝ] ℝ) (v : Plane) (hv : l v ≠ 0) (p : ℕ → Fin n) (hk : 0 < k)
    (hcontact : ∀ i, i < k → G.graph.Adj (p i) (p (i+1)))
    (hback : ∀ i, i+2 ≤ k → p i ≠ p (i+2))
    (hflat : ∀ i, i ≤ k → l (G.point (p i)) = l (G.point (p 0))) : p k ≠ p 0 := by
  intro he
  have hd := G.flat_chain_displacement l v hv p hk hcontact hback hflat
  rw [he] at hd
  let u := G.point (p 1)-G.point (p 0)
  have hu : ‖u‖ = 1 := by simpa only [u,← dist_eq_norm] using (hcontact 0 hk).symm.2
  have hune : u ≠ 0 := by intro hz; rw [hz,norm_zero] at hu; norm_num at hu
  have hz : (k : ℝ) • u = 0 := by
    calc
      _ = (G.point (p 0)+(k : ℝ) • u)-G.point (p 0) := by abel
      _ = G.point (p 0)-G.point (p 0) := congrArg (fun z => z-G.point (p 0)) hd.symm
      _ = 0 := sub_self _
  have hscalar : (k : ℝ) = 0 := (smul_eq_zero.mp hz).resolve_right hune
  have hpositive : (0 : ℝ) < k := by exact_mod_cast hk
  linarith

theorem PennyGraph.monotone_chain_index_injective {n k : ℕ} (G : PennyGraph n)
    (l : Plane →ₗ[ℝ] ℝ) (v : Plane) (hv : l v ≠ 0) (p : ℕ → Fin n)
    (hcontact : ∀ i, i < k → G.graph.Adj (p i) (p (i+1)))
    (hback : ∀ i, i+2 ≤ k → p i ≠ p (i+2))
    (hmono : Monotone (fun i : ℕ => l (G.point (p i)))) :
    ∀ i, i ≤ k → ∀ j, j ≤ k → p i = p j → i = j := by
  have hne (i j : ℕ) (hij : i < j) (hjk : j ≤ k) : p i ≠ p j := by
    intro he
    let q (t : ℕ) := p (i+t)
    have hd : 0 < j-i := by omega
    have hqcontact : ∀ t, t < j-i → G.graph.Adj (q t) (q (t+1)) := by
      intro t ht
      simpa only [q,Nat.add_assoc] using hcontact (i+t) (by omega)
    have hqback : ∀ t, t+2 ≤ j-i → q t ≠ q (t+2) := by
      intro t ht
      simpa only [q,Nat.add_assoc] using hback (i+t) (by omega)
    have hqflat : ∀ t, t ≤ j-i → l (G.point (q t)) = l (G.point (q 0)) := by
      intro t ht
      change l (G.point (p (i+t))) = l (G.point (p (i+0)))
      rw [Nat.add_zero]
      apply le_antisymm
      · calc
          _ ≤ l (G.point (p j)) := hmono (by omega)
          _ = _ := congrArg (fun a => l (G.point a)) he.symm
      · exact hmono (by omega)
    have hno := G.flat_chain_no_return l v hv q hd hqcontact hqback hqflat
    apply hno
    change p (i+(j-i)) = p (i+0)
    simpa only [show i+(j-i)=j by omega,Nat.add_zero] using he.symm
  intro i hi j hj he
  rcases lt_trichotomy i j with h | h | h
  · exact False.elim (hne i j h hj he)
  · exact h
  · exact False.elim (hne j i h hi he.symm)

theorem PennyGraph.walk_projection_monotone {n : ℕ} (G : PennyGraph n)
    (l : Plane →ₗ[ℝ] ℝ) {a b : Fin n} (q : G.graph.Walk a b)
    (hprojection : ∀ i, i < q.length →
      0 ≤ l (G.point (q.getVert (i+1))-G.point (q.getVert i))) :
    Monotone (fun i : ℕ => l (G.point (q.getVert i))) := by
  apply monotone_nat_of_le_succ
  intro i
  by_cases hi : i < q.length
  · have h := hprojection i hi
    rwa [map_sub,sub_nonneg] at h
  · rw [q.getVert_of_length_le (by omega),q.getVert_of_length_le (by omega)]

theorem PennyGraph.cap_strip_cross_zero_mem_trace {n : ℕ} (G : PennyGraph n)
    (l : Plane →ₗ[ℝ] ℝ) (a b : Fin n) (hab : G.graph.Adj a b)
    (hpositive : 0 < l (G.point b-G.point a)) (z : Plane)
    (hlo : 0 ≤ l (z-G.point a)) (hhi : l (z-G.point a) ≤ l (G.point b-G.point a))
    (hcross : cross2 (G.point b-G.point a) (z-G.point a) = 0) : z ∈ G.edgeTrace a b := by
  let v := G.point b-G.point a
  let w := z-G.point a
  let t := inner ℝ v w
  have hv : ‖v‖ = 1 := by simpa only [v,← dist_eq_norm] using hab.symm.2
  have hdec : w = t • v := by
    have hc : cross2 v w = 0 := hcross
    simpa only [hc,zero_smul,add_zero,t] using unit_direction_decomposition v w hv
  have hl : l w = t*l v := by rw [hdec,map_smul,smul_eq_mul]
  have ht : t = l w/l v := (eq_div_iff hpositive.ne').mpr hl.symm
  have ht0 : 0 ≤ t := by rw [ht]; exact div_nonneg hlo hpositive.le
  have ht1 : t ≤ 1 := by rw [ht]; apply (div_le_iff₀ hpositive).mpr; simpa only [one_mul] using hhi
  refine ⟨t,⟨ht0,ht1⟩,?_⟩
  change (1-t) • G.point a+t • G.point b = z
  calc
    _ = G.point a+t • v := by dsimp [v]; module
    _ = z := by rw [← hdec]; dsimp [w]; abel

theorem PennyGraph.cap_strip_collinear_vertex_eq_endpoint {n : ℕ} (G : PennyGraph n)
    (l : Plane →ₗ[ℝ] ℝ) (a b : Fin n) (hab : G.graph.Adj a b)
    (hpositive : 0 < l (G.point b-G.point a)) (c : Fin n)
    (hlo : 0 ≤ l (G.point c-G.point a))
    (hhi : l (G.point c-G.point a) ≤ l (G.point b-G.point a))
    (hcross : cross2 (G.point b-G.point a) (G.point c-G.point a) = 0) : c = a ∨ c = b := by
  obtain ⟨t,⟨ht0,ht1⟩,hparam⟩ := G.cap_strip_cross_zero_mem_trace l a b hab hpositive (G.point c) hlo hhi hcross
  by_cases h0 : t = 0
  · left
    apply G.point_injective
    simpa [PennyGraph.edgePoint,h0] using hparam.symm
  by_cases h1 : t = 1
  · right
    apply G.point_injective
    simpa [PennyGraph.edgePoint,h1] using hparam.symm
  exact False.elim (G.edgePoint_ne_vertex a b c hab
    (lt_of_le_of_ne ht0 (Ne.symm h0)) (lt_of_le_of_ne ht1 h1) hparam)

end Swanepoel
