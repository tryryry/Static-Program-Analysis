package pascal.taie.analysis.graph.callgraph;

import pascal.taie.World;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;

import java.util.*;
import java.util.stream.Stream;

/**
 * Implementation of the CHA algorithm.
 */
class CHABuilder implements CGBuilder<Invoke, JMethod> {

    private ClassHierarchy hierarchy;

    @Override
    public CallGraph<Invoke, JMethod> build() {
        hierarchy = World.getClassHierarchy();
        return buildCallGraph(World.getMainMethod());
    }

    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
        DefaultCallGraph callGraph = new DefaultCallGraph();
        callGraph.addEntryMethod(entry);
        // TODO -finish me
        Queue<JMethod>jMethods=new LinkedList<>();
        jMethods.add(entry);
        while(!jMethods.isEmpty()){
            JMethod method=jMethods.remove();
            if(!callGraph.contains(method)){
                callGraph.addReachableMethod(method);
                Stream<Invoke> callSite=callGraph.callSitesIn(method);
                callSite.forEach(call->{
                    Set<JMethod>methods=resolve(call);
                    methods.forEach(m->{
                        CallKind kind;
                        if(call.isStatic()){
                            kind=CallKind.STATIC;
                        }else if(call.isSpecial()){
                            kind=CallKind.SPECIAL;
                        }else if(call.isInterface()){
                            kind=CallKind.INTERFACE;
                        }else if(call.isVirtual()){
                            kind=CallKind.VIRTUAL;
                        }else{
                            kind=CallKind.OTHER;
                        }
                        if(m != null){
                            Edge<Invoke,JMethod> edge=new Edge<>(kind,call,m);
                            callGraph.addEdge(edge);
                            jMethods.add(m);
                        }

                    });
                });
            }
        }

        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        // TODO - finish me
        // return null;
        Set<JMethod> set = new LinkedHashSet<>();
        if(callSite.isStatic()){
            JClass jClass=callSite.getMethodRef().getDeclaringClass();
            Subsignature subsignature=callSite.getMethodRef().getSubsignature();
            JMethod jMethod=jClass.getDeclaredMethod(subsignature);
            set.add(jMethod);
        }else if(callSite.isSpecial()){
            JClass jClass=callSite.getMethodRef().getDeclaringClass();
            Subsignature subsignature=callSite.getMethodRef().getSubsignature();
            JMethod jMethod=dispatch(jClass,subsignature);
            set.add(jMethod);
        }else if(callSite.isVirtual()||callSite.isInterface()){
            Queue<JClass>jClasses=new LinkedList<>();
            JClass jClass=callSite.getMethodRef().getDeclaringClass();
            Subsignature subsignature=callSite.getMethodRef().getSubsignature();
            jClasses.add(jClass);

            if(!jClass.isInterface()){
               while(!jClasses.isEmpty()){
                   JClass Class=jClasses.remove();
                   JMethod jMethod=dispatch(Class,subsignature);
                   set.add(jMethod);
                   Collection<JClass>subClass=hierarchy.getDirectSubclassesOf(Class);
                   if(!subClass.isEmpty()){
                       for(JClass sub:subClass){
                           jClasses.add(sub);
                       }
                   }
               }
            }else{
                while(!jClasses.isEmpty()){
                    JClass Class=jClasses.remove();
                    JMethod jMethod=dispatch(Class,subsignature);
                    set.add(jMethod);
                    Collection<JClass>subImplement=hierarchy.getDirectImplementorsOf(Class);
                    Collection<JClass>subInterface=hierarchy.getDirectSubinterfacesOf(Class);
                    if(!subImplement.isEmpty()){
                        for(JClass sub:subImplement){
                            jClasses.add(sub);
                        }
                    }
                    if(!subInterface.isEmpty()){
                        for(JClass sub:subInterface){
                            jClasses.add(sub);
                        }
                    }
                }
            }

        }
        return set;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        // TODO - finish me
        //return null;
        if(jclass==null){
            return null;
        }
        JMethod jMethod=jclass.getDeclaredMethod(subsignature);
        if(jMethod!=null&&!jMethod.isAbstract()){
            return jMethod;
        }else{
            return dispatch(jclass.getSuperClass(),subsignature);
        }
    }
}
