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
FRONTEND_OBJ_BASENAMES_cppgm++ := pptoken_lib pp_token posttoken_support posttoken_pipeline ctrlexpr_support macro_support preproc_support pa10_support pa10_parser pa10_decls pa10_types pa10_expr pa11_model pa11_support pa11_parser pa11_emit pa12_support pa12_model pa12_decls pa12_types pa12_records pa12_statements pa12_expr pa12_expr_semantics pa12_expr_nodes pa12_expr_pointer pa12_names pa14_lowir pa14_lowir_call pa14_lowir_expr pa14_lowir_init pa14_lowir_support pa14_lowir_program
FRONTEND_OBJ_BASENAMES_lowiropt :=
FRONTEND_OBJ_BASENAMES_lowir2cy86 := lowir2cy86_model lowir2cy86_parser lowir2cy86_validate lowir2cy86_emit lowir2cy86_support
FRONTEND_OBJ_BASENAMES_lowir2native :=
