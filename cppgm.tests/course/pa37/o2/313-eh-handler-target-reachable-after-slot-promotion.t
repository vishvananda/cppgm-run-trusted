EH handler targets remain reachable across successor blocks during O2 slot promotion
declare function @may_throw() -> void [binding=strong]

function @f() -> i32 [binding=strong] {
  slot $flag : i32

  block ^entry:
    store i32 1, $flag
    eh_try ^cleanup
    jump ^body

  block ^body:
    call void @may_throw()
    eh_end
    return i32 0

  block ^cleanup:
    %v = load i32 $flag
    resume
}
