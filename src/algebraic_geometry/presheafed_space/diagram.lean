/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebraic_geometry.presheafed_space
import topology.category.Top.limits
import category_theory.limits.functor_category


universes v u

open category_theory
open Top
open Top.presheaf
open topological_space
open opposite
open category_theory.category
open category_theory.limits
open category_theory.functor

variables {J : Type v} [small_category J]
variables {C : Type u} [category.{v} C] [has_limits C]


namespace algebraic_geometry

-- TODO move
instance (X : Top) : has_limits (presheaf C X) := by { dsimp [presheaf], apply_instance, }

@[simp]
lemma bar {X Y : PresheafedSpace C} {f g : X ⟶ Y} (e : f = g) (U) :
  f.c.app (op U) = g.c.app (op U) ≫ (pushforward_eq (congr_arg PresheafedSpace.hom.base e.symm) X.𝒪).hom.app (op U) :=
begin
  subst e,
  simp only [pushforward_eq_rfl, comp_id],
end

@[simp]
lemma foo (F : J ⥤ PresheafedSpace C) (j) (U) : (F.map (𝟙 j)).c.app (op U) =
  (pushforward.id (F.obj j).𝒪).inv.app (op U) ≫ (pushforward_eq (by { simp, refl }) (F.obj j).𝒪).hom.app (op U) :=
begin
  cases U,
  dsimp,
  simp [bar (F.map_id j)],
  refl,
end

@[simp]
lemma foo' (F : J ⥤ PresheafedSpace C) {j₁ j₂ j₃} (f : j₁ ⟶ j₂) (g : j₂ ⟶ j₃) (U) : (F.map (f ≫ g)).c.app (op U) =
  (F.map g).c.app (op U) ≫ begin refine (pushforward_map (F.map g).base _).app _, refine (F.map f).c, end ≫ (pushforward.comp (F.obj j₁).𝒪 (F.map f).base (F.map g).base).inv.app (op U) ≫
    begin refine (pushforward_eq _ _).hom.app _, erw F.map_comp, refl, end :=
begin
  cases U,
  dsimp,
  simp [bar (F.map_comp f g)],
  dsimp,
  erw id_comp,
end

/--
Given a diagram of presheafed spaces,
we can push all the presheaves forward to the colimit `X` of the underlying topological spaces,
obtaining a diagram in `(presheaf C X)ᵒᵖ`.
-/
@[simps]
def pushforward_diagram_to_colimit (F : J ⥤ PresheafedSpace C) :
  J ⥤ (presheaf C (colimit (F ⋙ PresheafedSpace.forget)))ᵒᵖ :=
{ obj := λ j, op ((F.obj j).𝒪.pushforward (colimit.ι (F ⋙ PresheafedSpace.forget) j)),
  map := λ j j' f,
  (pushforward_map (colimit.ι (F ⋙ PresheafedSpace.forget) j') (F.map f).c ≫
    (pushforward.comp (F.obj j).𝒪 ((F ⋙ PresheafedSpace.forget).map f)
      (colimit.ι (F ⋙ PresheafedSpace.forget) j')).inv ≫
    (pushforward_eq (colimit.w (F ⋙ PresheafedSpace.forget) f) (F.obj j).𝒪).hom).op,
  map_id' :=
  begin
    intro j,
    apply (op_equiv _ _).injective,
    ext U,
    op_induction U,
    cases U,
    dsimp,
    simp,
    dsimp,
    erw id_comp,
    simp,
  end,
  map_comp' :=
  begin
    intros j₁ j₂ j₃ f g,
    apply (op_equiv _ _).injective,
    ext U,
    op_induction U,
    cases U,
    dsimp,
    simp,
    dsimp,
    erw id_comp,
    erw id_comp,
    erw id_comp,
    simp,
    congr' 1,
    rw (F.map f).c.congr,
    swap 3,
    refine op ⟨⇑(colimit.ι (F ⋙ PresheafedSpace.forget) j₂) ⁻¹' U_val, _⟩,
    swap 3,
    apply unop_injective,
    simp [set.preimage_preimage],
    congr,
    funext,
    exact Top.colimit.w_apply (F ⋙ PresheafedSpace.forget) g _,
    swap 2,
    simp,
    refl,
  end, }

@[simps]
def colimit (F : J ⥤ PresheafedSpace C) : PresheafedSpace C :=
{ to_Top := colimit (F ⋙ PresheafedSpace.forget),
  𝒪 := limit (pushforward_diagram_to_colimit F).left_op, }

lemma quux {X Y Z : C} (f : X ⟶ Z) (g : X = Y) (h : Y ⟶ Z) :
  f = eq_to_hom g ≫ h ↔ eq_to_hom g.symm ≫ f = h :=
begin
  fsplit,
  intro w,
  rw w, simp,
  intro w,
  rw ←w, simp,
end

@[simps]
def colimit_cocone (F : J ⥤ PresheafedSpace C) : cocone F :=
{ X := colimit F,
  ι :=
  { app := λ j,
    { base := colimit.ι (F ⋙ PresheafedSpace.forget) j,
      c := limit.π _ (op j), },
    naturality' :=
    begin
      intros j j' f,
      dsimp,
      fapply PresheafedSpace.ext,
      { dsimp,
        simp,
        ext x,
        exact Top.colimit.w_apply _ f _, },
      { dsimp,
        ext U,
        op_induction U,
        dsimp,
        simp,
        -- erw [id_comp, id_comp],
        have := limit.w (pushforward_diagram_to_colimit F).left_op f.op,
        have := congr_arg nat_trans.app this,
        rw ←this,
        cases U,
        dsimp,
        simp,
        -- erw [id_comp],
        congr,
        dsimp [pushforward],
        rw quux,
        simp,
        refl,
         }
    end, }, }

def colimit_cocone_is_colimit (F : J ⥤ PresheafedSpace C) : is_colimit (colimit_cocone F) :=
{ desc := λ s,
  { base := colimit.desc (F ⋙ PresheafedSpace.forget) (PresheafedSpace.forget.map_cocone s),
    c :=
    begin
      dsimp,
      have := limit.lift (pushforward_diagram_to_colimit F).left_op _,
      have := pushforward_map _ this,
      convert this,
      -- I think we need to restrict to just open embeddings for this to work.
      repeat { sorry },
    end, },
  fac' := sorry,
  uniq' := sorry, }

end algebraic_geometry
