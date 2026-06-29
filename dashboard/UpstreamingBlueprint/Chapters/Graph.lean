import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Staging dependency graph (declarations)" =>

Staging-internal dependency graph of `MathlibStaging` declarations. Nodes with no staging dependencies are *ready* (directly upstreamable); nodes depending on other staging declarations are *blocked* until those land upstream.


:::definition "PresheafOfModules_Submodule_toPresheafOfModules"
`PresheafOfModules.Submodule.toPresheafOfModules` — depth 5, 5 transitive staging deps.
{uses "PresheafOfModules_Submodule"}[] {uses "PresheafOfModules_restrict__"}[] {uses "PresheafOfModules_Submodule_obj"}[] {uses "PresheafOfModules_Submodule_map_mem"}[]
:::

:::definition "PresheafOfModules_Submodule__"
`PresheafOfModules.Submodule.ι` — depth 6, 6 transitive staging deps.
{uses "PresheafOfModules_Submodule_toPresheafOfModules"}[] {uses "PresheafOfModules_Submodule"}[] {uses "PresheafOfModules_Submodule_obj"}[]
:::

:::definition "PresheafOfModules_Submodule"
`PresheafOfModules.Submodule` — depth 1, 1 transitive staging deps.
{uses "PresheafOfModules_restrict__"}[]
:::

:::definition "PresheafOfModules_Submodule_ext"
`PresheafOfModules.Submodule.ext` — depth 3, 3 transitive staging deps.
{uses "PresheafOfModules_Submodule"}[] {uses "PresheafOfModules_restrict__"}[] {uses "PresheafOfModules_Submodule_obj"}[]
:::

:::definition "PresheafOfModules_Submodule_sSup_obj"
`PresheafOfModules.Submodule.sSup_obj` — depth 5, 5 transitive staging deps.
{uses "PresheafOfModules_Submodule"}[] {uses "PresheafOfModules_Submodule_instCompleteLattice"}[] {uses "PresheafOfModules_Submodule_obj"}[]
:::

:::definition "PresheafOfModules_Submodule_bot_obj"
`PresheafOfModules.Submodule.bot_obj` — depth 5, 5 transitive staging deps.
{uses "PresheafOfModules_Submodule"}[] {uses "PresheafOfModules_Submodule_instCompleteLattice"}[] {uses "PresheafOfModules_Submodule_obj"}[]
:::

:::definition "PresheafOfModules_Submodule_ext_iff"
`PresheafOfModules.Submodule.ext_iff` — depth 4, 4 transitive staging deps.
{uses "PresheafOfModules_Submodule"}[] {uses "PresheafOfModules_Submodule_ext"}[] {uses "PresheafOfModules_Submodule_obj"}[]
:::

:::definition "PresheafOfModules_Submodule_sInf_obj"
`PresheafOfModules.Submodule.sInf_obj` — depth 5, 5 transitive staging deps.
{uses "PresheafOfModules_Submodule"}[] {uses "PresheafOfModules_Submodule_instCompleteLattice"}[] {uses "PresheafOfModules_Submodule_obj"}[]
:::

:::definition "PresheafOfModules_Submodule_instCompleteLattice"
`PresheafOfModules.Submodule.instCompleteLattice` — depth 4, 4 transitive staging deps.
{uses "PresheafOfModules_Submodule"}[] {uses "PresheafOfModules_Submodule_obj"}[] {uses "PresheafOfModules_Submodule_instPartialOrder"}[]
:::

:::definition "PresheafOfModules_Submodule_toPresheafOfModules_map_apply"
`PresheafOfModules.Submodule.toPresheafOfModules_map_apply` — depth 6, 6 transitive staging deps.
{uses "PresheafOfModules_Submodule_toPresheafOfModules"}[] {uses "PresheafOfModules_Submodule"}[] {uses "PresheafOfModules_Submodule_obj"}[]
:::

:::definition "PresheafOfModules_restrict___apply"
`PresheafOfModules.restrictₛₗ_apply` — depth 1, 1 transitive staging deps.
{uses "PresheafOfModules_restrict__"}[]
:::

:::definition "PresheafOfModules_Submodule_le_iff"
`PresheafOfModules.Submodule.le_iff` — depth 4, 4 transitive staging deps.
{uses "PresheafOfModules_Submodule"}[] {uses "PresheafOfModules_Submodule_obj"}[] {uses "PresheafOfModules_Submodule_instPartialOrder"}[]
:::

:::definition "PresheafOfModules_restrict__"
`PresheafOfModules.restrictₛₗ` — depth 0, 0 transitive staging deps.
:::

:::definition "PresheafOfModules_Submodule___app_hom_apply"
`PresheafOfModules.Submodule.ι_app_hom_apply` — depth 7, 7 transitive staging deps.
{uses "PresheafOfModules_Submodule_toPresheafOfModules"}[] {uses "PresheafOfModules_Submodule__"}[] {uses "PresheafOfModules_Submodule"}[] {uses "PresheafOfModules_Submodule_obj"}[]
:::

:::definition "PresheafOfModules_Submodule_map"
`PresheafOfModules.Submodule.map` — depth 3, 3 transitive staging deps.
{uses "PresheafOfModules_Submodule"}[] {uses "PresheafOfModules_restrict__"}[] {uses "PresheafOfModules_Submodule_obj"}[]
:::

:::definition "PresheafOfModules_Submodule_obj"
`PresheafOfModules.Submodule.obj` — depth 2, 2 transitive staging deps.
{uses "PresheafOfModules_Submodule"}[]
:::

:::definition "PresheafOfModules_Submodule_top_obj"
`PresheafOfModules.Submodule.top_obj` — depth 5, 5 transitive staging deps.
{uses "PresheafOfModules_Submodule"}[] {uses "PresheafOfModules_Submodule_instCompleteLattice"}[] {uses "PresheafOfModules_Submodule_obj"}[]
:::

:::definition "PresheafOfModules_Submodule_sup_obj"
`PresheafOfModules.Submodule.sup_obj` — depth 5, 5 transitive staging deps.
{uses "PresheafOfModules_Submodule"}[] {uses "PresheafOfModules_Submodule_instCompleteLattice"}[] {uses "PresheafOfModules_Submodule_obj"}[]
:::

:::definition "PresheafOfModules_Submodule_toPresheafOfModules_obj"
`PresheafOfModules.Submodule.toPresheafOfModules_obj` — depth 6, 6 transitive staging deps.
{uses "PresheafOfModules_Submodule_toPresheafOfModules"}[] {uses "PresheafOfModules_Submodule"}[] {uses "PresheafOfModules_Submodule_obj"}[]
:::

:::definition "PresheafOfModules_Submodule_map_mem"
`PresheafOfModules.Submodule.map_mem` — depth 4, 4 transitive staging deps.
{uses "PresheafOfModules_Submodule"}[] {uses "PresheafOfModules_Submodule_map"}[] {uses "PresheafOfModules_Submodule_obj"}[]
:::

:::definition "Submodule_comap_iInf_"
`Submodule.comap_iInf'` — depth 0, 0 transitive staging deps.
:::

:::definition "PresheafOfModules_Submodule_inf_obj"
`PresheafOfModules.Submodule.inf_obj` — depth 5, 5 transitive staging deps.
{uses "PresheafOfModules_Submodule"}[] {uses "PresheafOfModules_Submodule_instCompleteLattice"}[] {uses "PresheafOfModules_Submodule_obj"}[]
:::

:::definition "PresheafOfModules_Submodule_instMono_"
`PresheafOfModules.Submodule.instMonoι` — depth 7, 7 transitive staging deps.
{uses "PresheafOfModules_Submodule_toPresheafOfModules"}[] {uses "PresheafOfModules_Submodule__"}[] {uses "PresheafOfModules_Submodule"}[] {uses "PresheafOfModules_Submodule_obj"}[]
:::

:::definition "PresheafOfModules_Submodule_instPartialOrder"
`PresheafOfModules.Submodule.instPartialOrder` — depth 3, 3 transitive staging deps.
{uses "PresheafOfModules_Submodule"}[] {uses "PresheafOfModules_Submodule_obj"}[]
:::
