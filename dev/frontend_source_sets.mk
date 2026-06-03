# Per-tool implementation source lists for the compiler.
#
# Add dev/src/foo.cpp to the tools that use it by adding `foo` below. For
# subdirectories, use the path without `.cpp`, such as `parser/foo`.

FRONTEND_SOURCE_SET_TARGETS := abimangle pptoken posttoken ctrlexpr macro preproc recog nsdecl nsinit cy86 cppgm++ lowiropt lowir2cy86 lowir2native

FRONTEND_OBJ_BASENAMES_abimangle :=
FRONTEND_OBJ_BASENAMES_pptoken := pptoken_lib
FRONTEND_OBJ_BASENAMES_posttoken := pptoken_lib pp_token posttoken_support posttoken_pipeline
FRONTEND_OBJ_BASENAMES_ctrlexpr := pptoken_lib pp_token posttoken_support ctrlexpr_support
FRONTEND_OBJ_BASENAMES_macro := pptoken_lib pp_token posttoken_support posttoken_pipeline macro_support
FRONTEND_OBJ_BASENAMES_preproc := pptoken_lib pp_token posttoken_support posttoken_pipeline ctrlexpr_support macro_support preproc_support
FRONTEND_OBJ_BASENAMES_recog := pptoken_lib pp_token posttoken_support posttoken_pipeline ctrlexpr_support macro_support preproc_support recog_grammar recog_support
FRONTEND_OBJ_BASENAMES_nsdecl := pptoken_lib pp_token posttoken_support posttoken_pipeline ctrlexpr_support macro_support preproc_support nsdecl_model nsdecl_parser nsdecl_support
FRONTEND_OBJ_BASENAMES_nsinit := pptoken_lib pp_token posttoken_support posttoken_pipeline ctrlexpr_support macro_support preproc_support nsinit_model nsinit_eval nsinit_parser nsinit_image nsinit_support
FRONTEND_OBJ_BASENAMES_cy86 := pptoken_lib pp_token posttoken_support posttoken_pipeline ctrlexpr_support macro_support preproc_support cy86_model cy86_parser cy86_x86 cy86_support
FRONTEND_OBJ_BASENAMES_cppgm++ := pptoken_lib pp_token posttoken_support posttoken_pipeline ctrlexpr_support macro_support preproc_support pa10_support pa10_parser pa10_decls pa10_types pa10_expr pa11_model pa11_support pa11_parser pa11_emit
FRONTEND_OBJ_BASENAMES_lowiropt :=
FRONTEND_OBJ_BASENAMES_lowir2cy86 :=
FRONTEND_OBJ_BASENAMES_lowir2native :=
