################################################################################
#                                MODEL COPYING
################################################################################
# extentsion point for model copying
function _copy_model(
    model::M
    ) where {M <: JuMP.AbstractModel}
    return M()
end