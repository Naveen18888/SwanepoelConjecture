module
public import Swanepoel.FaceCounts
@[expose] public section

noncomputable section
namespace Swanepoel

private def planeBox (R : ℝ) : Set Plane := {z | |z 0|≤R ∧ |z 1|≤R}

private theorem planeBox_bounded {R : ℝ} (hR : 0≤R) : Bornology.IsBounded (planeBox R) := by
  apply (Metric.isBounded_closedBall (x := (0 : Plane)) (r := 2*R)).subset
  rintro z ⟨h0,h1⟩
  have he : ‖z‖^2=(z 0)^2+(z 1)^2 := by
    simp [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_two]
  rw [Metric.mem_closedBall,dist_zero_right]
  obtain ⟨h0l,h0r⟩ := abs_le.mp h0
  obtain ⟨h1l,h1r⟩ := abs_le.mp h1
  nlinarith [norm_nonneg z,mul_nonneg (by linarith : 0≤R-z 0) (by linarith : 0≤R+z 0),
    mul_nonneg (by linarith : 0≤R-z 1) (by linarith : 0≤R+z 1)]

private theorem planeBox_compl_preconnected {R : ℝ} (_hR : 0≤R) :
    IsPreconnected (planeBox R)ᶜ := by
  let A : Set Plane := {z | R<z 0}
  let B : Set Plane := {z | R<z 1}
  let C : Set Plane := {z | z 0< -R}
  let D : Set Plane := {z | z 1< -R}
  have hA : IsPreconnected A :=
    ((convex_Ioi R).linear_preimage (EuclideanSpace.proj (0 : Fin 2)).toLinearMap).isPreconnected
  have hB : IsPreconnected B :=
    ((convex_Ioi R).linear_preimage (EuclideanSpace.proj (1 : Fin 2)).toLinearMap).isPreconnected
  have hC : IsPreconnected C :=
    ((convex_Iio (-R)).linear_preimage (EuclideanSpace.proj (0 : Fin 2)).toLinearMap).isPreconnected
  have hD : IsPreconnected D :=
    ((convex_Iio (-R)).linear_preimage (EuclideanSpace.proj (1 : Fin 2)).toLinearMap).isPreconnected
  let p : Plane := EuclideanSpace.single 0 (R+1)+EuclideanSpace.single 1 (R+1)
  let q : Plane := EuclideanSpace.single 0 (-R-1)+EuclideanSpace.single 1 (R+1)
  let r : Plane := EuclideanSpace.single 0 (R+1)+EuclideanSpace.single 1 (-R-1)
  have hpA : p∈A := by simp [p,A]
  have hpB : p∈B := by simp [p,B]
  have hqB : q∈B := by simp [q,B]
  have hqC : q∈C := by simp [q,C]
  have hrA : r∈A := by simp [r,A]
  have hrD : r∈D := by simp [r,D]
  have hu := ((hA.union p hpA hpB hB).union q (Or.inr hqB) hqC hC).union r
    (Or.inl (Or.inl hrA)) hrD hD
  have he : A ∪ B ∪ C ∪ D=(planeBox R)ᶜ := by
    ext z
    simp only [A,B,C,D,planeBox,Set.mem_union,Set.mem_compl_iff,Set.mem_ofPred_eq,abs_le]
    constructor
    · rintro (((h | h) | h) | h) <;> intro hz <;> linarith [hz.1.1,hz.1.2,hz.2.1,hz.2.2]
    · intro h
      by_contra hn
      push Not at hn
      exact h ⟨⟨by linarith [hn.1.2],by linarith [hn.1.1.1]⟩,
        ⟨by linarith [hn.2],by linarith [hn.1.1.2]⟩⟩
  rwa [he] at hu

private theorem planeBox_compl_unbounded {R : ℝ} (hR : 0≤R) :
    ¬Bornology.IsBounded (planeBox R)ᶜ := by
  intro hb
  have h := (planeBox_bounded hR).union hb
  rw [Set.union_compl_self] at h
  exact NormedSpace.unbounded_univ ℝ Plane h

theorem PennyGraph.drawing_subset_box {n : ℕ} (G : PennyGraph n) :
    ∃ R : ℝ, 0≤R ∧ ∀ z∈G.drawing, |z 0|≤R ∧ |z 1|≤R := by
  obtain ⟨R,hR⟩ := isBounded_iff_forall_norm_le.mp G.isCompact_drawing.isBounded
  refine ⟨max R 0,le_max_right _ _,?_⟩
  intro z hz
  have hcoord (i : Fin 2) : |z i|≤max R 0 := by
    have hi := PiLp.norm_apply_le z i
    rw [Real.norm_eq_abs] at hi
    exact hi.trans ((hR z hz).trans (le_max_left _ _))
  exact ⟨hcoord 0,hcoord 1⟩

theorem PennyGraph.exists_unique_outer_face {n : ℕ} (G : PennyGraph n) :
    ∃! F : PlaneFace G, ¬Bornology.IsBounded F.val := by
  classical
  obtain ⟨R,hR,hdraw⟩ := G.drawing_subset_box
  let E := (planeBox R)ᶜ
  have hE : IsPreconnected E := planeBox_compl_preconnected hR
  have hEu : ¬Bornology.IsBounded E := planeBox_compl_unbounded hR
  have hEc : E⊆G.drawingᶜ := by
    intro z hz hzd
    exact hz (hdraw z hzd)
  obtain ⟨p,hp⟩ := Bornology.nonempty_of_not_isBounded hEu
  let F : PlaneFace G := ⟨connectedComponentIn G.drawingᶜ p,⟨p,hEc hp,rfl⟩⟩
  have hEF : E⊆F.val := hE.subset_connectedComponentIn hp hEc
  have hFu : ¬Bornology.IsBounded F.val := fun hb => hEu (hb.subset hEF)
  refine ⟨F,hFu,?_⟩
  intro H hHu
  have hex : ∃ z, z∈H.val ∧ z∈E := by
    by_contra hn
    push Not at hn
    have hb : Bornology.IsBounded H.val := (planeBox_bounded hR).subset (by
      intro z hz
      exact not_not.mp (hn z hz))
    exact hHu hb
  obtain ⟨z,hzH,hzE⟩ := hex
  apply Subtype.ext
  exact (H.property.eq_component hzH).trans (F.property.eq_component (hEF hzE)).symm

theorem PennyGraph.all_face_count {n : ℕ} (G : PennyGraph n) :
    Nat.card (PlaneFace G)=Fintype.card (BoundedFace G)+1 := by
  classical
  let _ : Fintype (PlaneFace G) := Fintype.ofFinite _
  obtain ⟨outer,houter,huniq⟩ := G.exists_unique_outer_face
  have hu : Fintype.card {F : PlaneFace G // ¬Bornology.IsBounded F.val}=1 := by
    have h := Fintype.card_of_subtype ({outer} : Finset (PlaneFace G)) (by
      intro F
      simp only [Finset.mem_singleton]
      exact ⟨fun h => h ▸ houter,fun h => huniq F h⟩)
    simpa only [Finset.card_singleton] using h
  let e : {F : PlaneFace G // Bornology.IsBounded F.val} ≃ BoundedFace G :=
    { toFun F := ⟨F.val.val,F.val.property,F.property⟩
      invFun F := ⟨⟨F.val,F.property.1⟩,F.property.2⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  have hb := Fintype.card_congr e
  have ht := Fintype.card_subtype_compl (fun F : PlaneFace G => Bornology.IsBounded F.val)
  simp only [← Nat.card_eq_fintype_card] at hu hb ht ⊢
  omega

end Swanepoel
