let template_type = variable::get("template_type");
if template_type == "default" {
    variable::set("revocable_by_others", true);
    variable::set("restorable", true);
}