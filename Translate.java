package M3;

import java.io.PrintWriter;
import java.util.*;

import Translate.*;
import Translate.Temp.Label;

class Translate {
    private static void usage() {
        throw new Error("Usage: java M3.Translate "
            + "[ -target= Mips|PPCDarwin|PPCLinux ] <source>.java");
    }

    static Frame target;
    public static void main(String[] args) {
        target = new Mips.Frame();
        boolean main = false;
        if (args.length < 1) usage();
        if (args.length > 1)
            for (String arg : args) {
                if (arg.equals("-main"))
                    main = true;
                else if (arg.equals("-target=Mips"))
                    target = new Mips.Frame();
                else if (arg.equals("-target=PPCDarwin"))
                    target = new PPC.Frame.Darwin();
                else if (arg.equals("-target=PPCLinux"))
                    target = new PPC.Frame.Linux();
                else if (arg.startsWith("-"))
                    usage();
            }
        java.io.File file = new java.io.File(args[args.length - 1]);
        try {
            Value.Module module = Semant.TypeCheck(file);
            if (Semant.anyErrors) return;
            List<Frag> frags = Compile(module, main);
            if (Semant.anyErrors) return;
            PrintWriter out = new PrintWriter(System.out);
            for (Frag f : frags) {
              out.println(f);
              out.flush();
            }
        } catch (ParseException e) {
            System.err.println(e.getMessage());
        } catch (TokenMgrError e) {
            System.err.println(e.getMessage());
        }
        System.err.flush();
    }

    static LinkedList<Frag> frags = new LinkedList<Frag>();
    static List<Frag> Compile(final Value.Module m, boolean main) {
        String bodyName = m.name + (m.isInterface ? "_I3" : "_M3");
        ProcBody body = new ProcBody(bodyName) {
            void emitDecl() {}
            void emitBody() {
                currentFrame = this.frame;
                returnLabel = null;
                Tree.Stm stm = null;
                stm = SEQ(stm, InitValues(m.imports));
                stm = SEQ(stm, InitValues(m.locals));
                // initialize my exported variables
                stm = SEQ(stm, InitGlobals(m.externals));
                // perform the main body
                for (Absyn.Expr.Stmt s : m.decl.stmts) {
                    stm = SEQ(stm, Compile(s).unNx());
                }
                frags.add(new Frag.Proc(stm, this.frame));
            }
        };
        for (Scope s: m.locals.children)
            if (s.proc != null) ProcBodies(s);
        ProcBody.Push(body);
        ProcBodies(m.body);
        ProcBody.Pop();

        Scope zz = Scope.Push(m.locals);
        body.emitDecl();
        for (Type t : m.types) Compile(t);
        // declare my imports, exports and local variables
        for (Value.External.Port p : m.externals.imports.values()) {
            EnterScope(p.module.locals);
        }
        EnterScope(m.imports);
        EnterScope(m.locals);
        // generate any internal procedures
        ProcBody.EmitAll();
        Scope.Pop(zz);

        if (!main) return frags;

        // generate code for main method
        {
            Frame frame = target.newFrame("main", null);
            Tree.Stm stm = ESTM(CALL(NAME(Temp.getLabel(body.name)), Exps()));
            frags.add(new Frag.Proc(stm, frame));
        }
        // generate code for helper functions
        {
            Frame frame = target.newFrame("new", null);
            Tree.Exp _size = frame.allocFormal(new Temp("_size")).exp(frame);
            Tree.Exp _head = frame.allocFormal(new Temp("_head")).exp(frame);
            Temp size = new Temp();
            Temp head = new Temp();
            Temp p = new Temp();
            Tree.Stm stm =
                SEQ(MOVE(TEMP(size), _size), //
                    MOVE(TEMP(head), _head), //
                    MOVE(TEMP(p), //
                         CALL(frame.external("malloc"), //
                              Exps(ADD(CONST(target.wordSize()), TEMP(size))))), //
                    MOVE(MEM(TEMP(p)), TEMP(head)), //
                    MOVE(TEMP(p), ADD(TEMP(p), CONST(target.wordSize()))), //
                    ESTM(CALL(frame.external("bzero"), //
                              Exps(TEMP(p), TEMP(size)))), //
                    MOVE(frame.RV(), TEMP(p)));
            frags.add(new Frag.Proc(stm, frame));
        }
        {
            Frame frame = target.newFrame("badPtr", null);
            Label msg = stringLabel("Attempt to use a null pointer");
            Tree.Stm stm =
                SEQ(ESTM(CALL(frame.external("puts"), Exps(NAME(msg)))),
                    ESTM(CALL(frame.external("exit"), Exps(CONST(1)))));
            frags.add(new Frag.Proc(stm, frame));
        }
        {
            Frame frame = target.newFrame("badSub", null);
            Label msg = stringLabel("Subscript out of bounds");
            Tree.Stm stm =
                SEQ(ESTM(CALL(frame.external("puts"), Exps(NAME(msg)))),
                    ESTM(CALL(frame.external("exit"), Exps(CONST(1)))));
            frags.add(new Frag.Proc(stm, frame));
        }
        return frags;
    }

    static Frame currentFrame;
    static Label returnLabel;

    static final Map<Value.Procedure,ProcBody> bodies = new HashMap<Value.Procedure,ProcBody>();
    static void ProcBodies(Scope scope) {
        if (scope == null) return;
        final Value.Procedure p = scope.proc;
        if (p != null && p.decl != null && p.decl.stmts != null) {
            ProcBody body = new ProcBody(Value.GlobalName(p)) {
                @Override
                void emitDecl() {
                    currentFrame = this.frame;
                    Declare(p);
                }
                void emitBody() {
                    returnLabel = new Temp.Label();
                    currentFrame = this.frame;
                    Tree.Stm stm = null;
                    Scope zz = Scope.Push(p.syms);
                    EnterScope(p.syms);
                    stm = SEQ(stm, InitValues(p.syms));
                    for (Absyn.Stmt stmt : p.decl.stmts) {
                        stm = SEQ(stm, Compile(stmt).unNx());
                    }
                    stm = SEQ(stm, LABEL(returnLabel));
                    Scope.Pop(zz);
                    frags.add(new Frag.Proc(stm, this.frame));
                }
            };
            bodies.put(p, body);
            ProcBody.Push(body);
        }
        for (Scope s: scope.children)
            ProcBodies(s);
        if (p != null && p.decl != null)
            ProcBody.Pop();
    }

    static Tree.Stm InitValues(Scope scope) {
        Tree.Stm stm = null;
        for (Value v : Scope.ToList(scope)) stm = SEQ(stm, LangInit(v));
        for (Value v : Scope.ToList(scope)) stm = SEQ(stm, UserInit(v));
        return stm;
    }

    static Tree.Stm InitGlobals(Value.External.Set set) {
        Tree.Stm stm = null;
        for (Value.External.Port p: set.exports.values())
            stm = SEQ(stm, InitExports(p.module));
        return stm;
    }

    static Tree.Stm InitExports(Value.Module m) {
        Tree.Stm stm = null;
        for (Value v : Scope.ToList(m.locals))
            if (v.exported)
                stm = SEQ(stm, InitGlobal(Value.Variable.Is(v)));
        return stm;
    }

    static Tree.Stm InitGlobal(Value.Variable v) {
        if (v == null) return null;
        if (!v.initDone && !v.external) {
            assert !Type.IsStructured(v.type);
            return MOVE(LoadLValue(v), CONST(0));
        }
        return null;
    }

    static Tree.Exp MEM(Tree.Exp exp) {
        return new Tree.Exp.MEM(exp, CONST(0));
    }

    static Tree.Exp MEM(Tree.Exp exp, int i) {
        return new Tree.Exp.MEM(exp, CONST(i));
    }

    static Tree.Exp TEMP(Temp temp) {
        return new Tree.Exp.TEMP(temp);
    }

    static Tree.Exp ESEQ(Tree.Stm stm, Tree.Exp exp) {
        return (stm == null) ? exp : new Tree.Exp.ESEQ(stm, exp);
    }

    static Tree.Exp NAME(Temp.Label label) {
        return new Tree.Exp.NAME(label);
    }

    static Tree.Exp.CONST CONST(int value) {
        return new Tree.Exp.CONST(value);
    }

    static Tree.Exp[] Exps(Tree.Exp... a) {
        return a;
    }

    static Tree.Exp CALL(Tree.Exp f, Tree.Exp[] a) {
        if (a.length > currentFrame.maxArgsOut)
            currentFrame.maxArgsOut = a.length;
        return new Tree.Exp.CALL(f, a);
    }

    static Tree.Exp ADD(Tree.Exp l, Tree.Exp r) {
        if (l instanceof Tree.Exp.CONST && ((Tree.Exp.CONST)l).value == 0)
            return r;
        if (r instanceof Tree.Exp.CONST && ((Tree.Exp.CONST)r).value == 0)
            return l;
        return new Tree.Exp.BINOP(Tree.Exp.BINOP.Operator.ADD, l, r);
    }

    static Tree.Exp AND(Tree.Exp l, Tree.Exp r) {
        return new Tree.Exp.BINOP(Tree.Exp.BINOP.Operator.AND, l, r);
    }

    static Tree.Exp DIV(Tree.Exp l, Tree.Exp r) {
        return new Tree.Exp.BINOP(Tree.Exp.BINOP.Operator.DIV, l, r);
    }

    static Tree.Exp DIVU(Tree.Exp l, Tree.Exp r) {
        return new Tree.Exp.BINOP(Tree.Exp.BINOP.Operator.DIVU, l, r);
    }

    static Tree.Exp MOD(Tree.Exp l, Tree.Exp r) {
        return new Tree.Exp.BINOP(Tree.Exp.BINOP.Operator.MOD, l, r);
    }

    static Tree.Exp MUL(Tree.Exp l, Tree.Exp r) {
        return new Tree.Exp.BINOP(Tree.Exp.BINOP.Operator.MUL, l, r);
    }

    static Tree.Exp OR(Tree.Exp l, Tree.Exp r) {
        return new Tree.Exp.BINOP(Tree.Exp.BINOP.Operator.OR, l, r);
    }

    static Tree.Exp SLL(Tree.Exp l, Tree.Exp r) {
        return new Tree.Exp.BINOP(Tree.Exp.BINOP.Operator.SLL, l, r);
    }

    static Tree.Exp SRA(Tree.Exp l, Tree.Exp r) {
        return new Tree.Exp.BINOP(Tree.Exp.BINOP.Operator.SRA, l, r);
    }

    static Tree.Exp SRL(Tree.Exp l, Tree.Exp r) {
        return new Tree.Exp.BINOP(Tree.Exp.BINOP.Operator.SRL, l, r);
    }

    static Tree.Exp SUB(Tree.Exp l, Tree.Exp r) {
        return new Tree.Exp.BINOP(Tree.Exp.BINOP.Operator.SUB, l, r);
    }

    static Tree.Exp XOR(Tree.Exp l, Tree.Exp r) {
        return new Tree.Exp.BINOP(Tree.Exp.BINOP.Operator.XOR, l, r);
    }

    static Tree.Stm SEQ(Tree.Stm l, Tree.Stm r) {
        if (l == null)
            return r;
        if (r == null)
            return l;
        return new Tree.Stm.SEQ(l, r);
    }

    static Tree.Stm SEQ(Tree.Stm... a) {
        Tree.Stm stm = null;
        for (Tree.Stm s : a)
            stm = SEQ(stm, s);
        return stm;
    }

    static Tree.Stm LABEL(Temp.Label label) {
        return new Tree.Stm.LABEL(label);
    }

    static Tree.Stm JUMP(Temp.Label target) {
        return new Tree.Stm.JUMP(target);
    }

    static Tree.Stm JUMP(Tree.Exp exp, Temp.Label[] targets) {
        return new Tree.Stm.JUMP(exp, targets);
    }

    static Tree.Stm MOVE(Tree.Exp d, Tree.Exp s) {
        return new Tree.Stm.MOVE(d, s);
    }

    static Tree.Stm ESTM(Tree.Exp exp) {
        return new Tree.Stm.ESTM(exp);
    }

    static Tree.Stm BEQ(Tree.Exp l, Tree.Exp r, Temp.Label t, Temp.Label f) {
        return new Tree.Stm.CJUMP(Tree.Stm.CJUMP.Operator.BEQ, l, r, t, f);
    }

    static Tree.Stm BGE(Tree.Exp l, Tree.Exp r, Temp.Label t, Temp.Label f) {
        return new Tree.Stm.CJUMP(Tree.Stm.CJUMP.Operator.BGE, l, r, t, f);
    }

    static Tree.Stm BGT(Tree.Exp l, Tree.Exp r, Temp.Label t, Temp.Label f) {
        return new Tree.Stm.CJUMP(Tree.Stm.CJUMP.Operator.BGT, l, r, t, f);
    }

    static Tree.Stm BLE(Tree.Exp l, Tree.Exp r, Temp.Label t, Temp.Label f) {
        return new Tree.Stm.CJUMP(Tree.Stm.CJUMP.Operator.BLE, l, r, t, f);
    }

    static Tree.Stm BLT(Tree.Exp l, Tree.Exp r, Temp.Label t, Temp.Label f) {
        return new Tree.Stm.CJUMP(Tree.Stm.CJUMP.Operator.BLT, l, r, t, f);
    }

    static Tree.Stm BNE(Tree.Exp l, Tree.Exp r, Temp.Label t, Temp.Label f) {
        return new Tree.Stm.CJUMP(Tree.Stm.CJUMP.Operator.BNE, l, r, t, f);
    }

    /**
     * This class manages the order that procedure bodies are emitted.
     * It also records the relative level of nested procedures.
     */
    static abstract class ProcBody {
        final String name;
        ProcBody(String name) {
            this.name = name;
        }

        private ProcBody parent;
        int level;
        private ProcBody sibling;
        private ProcBody children;
        protected Frame frame;

        abstract void emitDecl();
        abstract void emitBody();

        protected static ProcBody current;
        private static ProcBody head;
        private static ProcBody done;
        private static int depth = -1;

        /**
         * Push a procedure that will be written as a child of the current procedure.
         */
        static void Push(ProcBody t) {
            assert t.parent == null && t.sibling == null && t.children == null;
            t.level = ++depth;
            t.parent = current;
            if (current == null) {
                // depth == 0
                t.sibling = head;
                head = t;
                t.frame = target.newFrame(t.name, null);
            } else {
                t.sibling = current.children;
                current.children = t;
                t.frame = target.newFrame(t.name, current.frame);
            }
            current = t;
        }
        /**
         * Pops the current procedure.
         */
        static void Pop() {
            current = current.parent;
            depth--;
        }
        /**
         * Schedules 't' to be written as a top-level procedure.
         */
        static void Schedule(ProcBody t) {
            t.sibling = head;
            head = t;
        }
        /**
         * Generate all the procedure bodies.
         */
        static void EmitAll() {
            // generate the declarations and bodies
            while (head != null) {
                ProcBody t = head; head = null; // grab the guys that are waiting
                t = SourceOrder(t); // put 'em in source order
                EmitDecl(t); // generate their declarations
                EmitBody(t); // generate their bodies & build "done" list
            }
        }
        private static ProcBody SourceOrder(ProcBody t) {
            // reverse the list
            ProcBody a = t, b = null;
            while (a != null) {
                ProcBody c = a.sibling;
                a.sibling = b;
                b = a;
                a = c;
            }
            t = b;
            // recursively reorder the children
            while (t != null) {
                t.children = SourceOrder(t.children);
                t = t.sibling;
            }
            return b;
        }
        private static void EmitDecl(ProcBody t) {
            while (t != null) {
                t.emitDecl();
                EmitDecl(t.children);
                t = t.sibling;
            }
        }
        private static void EmitBody(ProcBody t) {
            while (t != null) {
                t.emitBody();
                EmitBody(t.children);
                // move to the next sibling, but leave this guy on the "done" list
                ProcBody a = t.sibling;
                t.sibling = done; done = t;
                t = a;
            }
        }
    }

    /**
     * Generate declarations for all the values in a scope.
     * Generate procedure declarations after non-procedure declarations.
     */
    static void EnterScope(Scope scope) {
        if (scope == null) return;
        for (Value v : Scope.ToList(scope))
            if (Value.Procedure.Is(v) == null)
                Declare(v);
        for (Value v : Scope.ToList(scope)) {
            if (Value.Procedure.Is(v) != null) {
                Declare(v);
            }
        }
    }

    /**
     * Every variable declaration has an associated accesss.
     * This map keeps track of them. 
     */
    static Map<Value.Variable,Frame.Access> accesses = new HashMap<Value.Variable,Frame.Access>();

    /**
     * Generate declaration for v.
     */
    static void Declare(Value v) {
        class Visitor implements Value.Visitor<Void> {
            public Void visit(Value.Field v) { return null; }
            public Void visit(Value.Formal v) { return null; }
            public Void visit(Value.Method v) { return null; }
            public Void visit(Value.Module v) { return null; }
            public Void visit(final Value.Procedure v) {
                Type.Proc sig = v.signature;
                if (v.intf_peer != null) {
                    sig = v.intf_peer.signature;
                    Compile(sig);
                }
                Compile(v.signature);
                // try to compile the imported type first

                ProcBody body = bodies.get(v);
                if (body == null) {
                    // it's not a local procedure
                    if (v.impl_peer != null) {
                        // it's an interface procedure that's implemented in this module
                        visit(v.impl_peer);
                        return null;
                    } else {
                        // it's an imported procedure
                        ImportProc(v);
                        return null;
                    }
                }
                currentFrame = body.frame;
                Scope zz = Scope.Push(v.syms);
                EnterScope(v.syms);
                Scope.Pop(zz);
                return null;
            }
            void ImportProc(Value.Procedure v) {
                if (v.syms != null) {
                    Scope zz = Scope.Push(v.syms);
                    EnterScope(v.syms);
                    Scope.Pop(zz);
                } else {
                    DeclareFormals(v);
                }
            }
            void DeclareFormals(Value.Procedure p) {
                // declare types for each of the formals
                for (Value v : Scope.ToList(p.signature.formals)) {
                    Value.Formal f = Value.Formal.Is(v);
                    Compile(Value.TypeOf(f));
                    if (f.mode != Value.Formal.Mode.VALUE || f.refType != null) {
                        Compile(f.refType);
                    }
                }
            }
            public Void visit(Value.Variable v) {
                Compile(v.type);
                // declare the actual variable
                if (v.external) {
                    // external
                } else if (v.imported) {
                    // imported
                } else if (v.toplevel) {
                    // global
                    Temp.Label l = Temp.getLabel(Value.GlobalName(v));
                    frags.add(new Frag.Data(target.record(l, 1)));
                    if (v.decl.expr == null) v.initDone = true;
                } else {
                    Temp t = null;
                    if (!v.up_level && !v.flags.contains(Value.Flags.needsAddress))
                        t = new Temp(Value.GlobalName(v));
                    if (v.formal == null) {
                        // simple local variable
                        accesses.put(v, currentFrame.allocLocal(t));
                    } else if (v.indirect) {
                        // formal passed by reference => param is an address
                        accesses.put(v, currentFrame.allocFormal(t));
                    } else {
                        // simple parameter
                        accesses.put(v, currentFrame.allocFormal(t));
                    }
                }
                return null;
            }
            public Void visit(Value.Constant v) {
                if (v.exported) Compile(v.type);
                return null;
            }
            public Void visit(Value.External v) {
                Value value = v.value;
                if (value != null) {
                    boolean i = value.imported;
                    boolean e = value.exported;
                    value.imported = v.imported;
                    value.exported = v.exported;
                    Declare(value);
                    value.imported = i;
                    value.exported = e;
                }
                return null;
            }
            public Void visit(Value.Tipe v) {
                Compile(v.value);
                return null;
            }
        }
        if (v == null) return;
        if (v.declared) return;
        v.declared = true;
        v.accept(new Visitor());
    }

    /**
     * Generate language-defined initialization code for v.
     */
    static Tree.Stm LangInit(Value v) {
        class Visitor implements Value.Visitor<Tree.Stm> {
            public Tree.Stm visit(Value.Constant v) { return null; }
            public Tree.Stm visit(Value.Module v) { return null; }
            public Tree.Stm visit(Value.Procedure v) { return null; }
            public Tree.Stm visit(Value.Tipe v) { return null; }
            public Tree.Stm visit(Value.External v) {
                return LangInit(v.value);
            }
            public Tree.Stm visit(Value.Field v) {
                Compile(v.type);
                return null;
            }
            public Tree.Stm visit(Value.Formal v) {
                Compile(v.type);
                Compile(v.refType);
                return null;
            }
            public Tree.Stm visit(Value.Method v) {
                Compile(v.signature);
                return null;
            }
            @Override
            public Tree.Stm visit(Value.Variable v) {
                Tree.Stm stm = null;
                if (v.imported || v.external) {
                    v.initDone = true;
                } else if (v.formal != null) {
                    if (v.indirect)
                        stm = SEQ(stm, CopyOpenArray(v, v.formal.refType));
                    // formal parameters don't need any further initialization
                    v.initDone = true;
                } else if (v.indirect && !v.toplevel) {
                    // WITH variable bound to a designator
                    v.initDone = true;
                }

                if (v.initDone) return stm;

                // initialize the value
                if (v.expr != null && !v.up_level && !v.imported) {
                    // variable has a user specified init value and isn't referenced
                    // by any nested procedures => try to avoid the language defined
                    // init and wait until we get to the user defined initialization.
                    v.initPending = true;
                }
                return stm;
            }
            Tree.Stm CopyOpenArray(Value.Variable v, Type t) {
                if (t == null) return null;
                Semant.error("open array passed by VALUE unimplemented");
                return null;
            }
        }
        if (v == null) return null;
        if (v.compiled) return null;
        assert v.checked;
        v.compiled = true;
        return v.accept(new Visitor());   
    }

    /**
     * Generate code to load v.
     */
    static Tree.Exp Load(Value v) {
        class Visitor implements Value.Visitor<Tree.Exp> {
            public Tree.Exp visit(Value.Field v) { assert false; return null; }
            public Tree.Exp visit(Value.Tipe v) { assert false; return null; }
            public Tree.Exp visit(Value.Module v) { assert false; return null; }
            public Tree.Exp visit(Value.Method v) { assert false; return null; }
            public Tree.Exp visit(Value.Formal v) {
                Semant.error(v.decl, "formal has no default value");
                return null;
            }
            public Tree.Exp visit(Value.Constant v) {
                return CONST(v.value);
            }
            public Tree.Exp visit(Value.Procedure v) {
                if (v.decl == null) Semant.error("builtin operation is not a procedure (" + v.name + ")");
                if (v.impl_peer != null) v = v.impl_peer;
                Declare(v);
                if (v.external)
                    return target.external(Value.GlobalName(v));
                else
                    return NAME(Temp.getLabel(Value.GlobalName(v)));
            }
            public Tree.Exp visit(Value.External v) {
                return Load(v.value);
            }
            public Tree.Exp visit(Value.Variable v) {
                return LoadLValue(v);
            }
        }
        if (v == null) return null;
        assert v.checked;
        return v.accept(new Visitor());
    }

    static Tree.Exp LoadLValue(Value.Variable v) {
        Declare(v);
        if (v.initPending) ForceInit(v);
        Frame.Access a = accesses.get(v);
        if (a == null) {
            Tree.Exp exp;
            assert v.toplevel;
            if (v.external)
                exp = target.external(Value.GlobalName(v));
            else
                exp = NAME(Temp.getLabel(Value.GlobalName(v)));
            if (v.indirect)
                exp = MEM(exp);
            return MEM(exp);
        } else if (v.indirect) {
            // TODO outer-scope nested variable access
            return MEM(a.exp(currentFrame));
        } else {
            // TODO outer-scope nested variable access
            return a.exp(currentFrame);
        }
    }

    static Tree.Stm ForceInit(Value.Variable v) {
        v.initPending = false;
        return InitValue(LoadLValue(v), v.type);
    }

    /**
     * Generate language-defined initialization value for a variable of type t.
     */
    static Tree.Stm InitValue(final Tree.Exp lvalue, Type t) {
        class Visitor implements Type.Visitor<Tree.Stm> {
            public Tree.Stm visit(Type.Named t) { assert false; return null; }
            public Tree.Stm visit(Type t) { return MOVE(lvalue, CONST(0)); }
            public Tree.Stm visit(Type.Enum t) { return MOVE(lvalue, CONST(0)); }
            public Tree.Stm visit(Type.Ref t) { return MOVE(lvalue, CONST(0)); }
            public Tree.Stm visit(Type.Proc t) { return MOVE(lvalue, CONST(0)); }
            public Tree.Stm visit(Type.Object t) { return MOVE(lvalue, CONST(0)); }
            public Tree.Stm visit(Type.OpenArray t) {
                assert false;
                return null;
            }
        }
        t = Type.Check(t);
        return t.accept(new Visitor());
    }

    /**
     * Generate user-defined initialization code for v. 
     */
    static Tree.Stm UserInit(Value v) {
        class Visitor implements Value.Visitor<Tree.Stm> {
            public Tree.Stm visit(Value.Field v) { return null; }
            public Tree.Stm visit(Value.Formal v) { return null; }
            public Tree.Stm visit(Value.Method v) { return null; }
            public Tree.Stm visit(Value.Procedure v) { return null; }
            public Tree.Stm visit(Value.Constant v) { return null;}
            public Tree.Stm visit(Value.Module v) { return null; }
            public Tree.Stm visit(Value.Tipe v) { return null; }
            public Tree.Stm visit(Value.Variable v) {
                Tree.Stm stm = null;
                if (v.expr != null && !v.initDone && !v.imported) {
                    v.initPending = false;
                    stm = MOVE(LoadLValue(v), Compile(v.expr).unEx());
                }
                v.initDone = true;
                return stm;
            }
            public Tree.Stm visit(Value.External v) {
                return UserInit(v.value);
            }
        }
        if (v == null) return null;
        return v.accept(new Visitor());
    }

    /**
     * Compile a type t.
     */
    static Map<Type,Type> compiled = new HashMap<Type,Type>();
    {
        compiled.put(Type.Check(Type.BOOLEAN),Type.BOOLEAN);
        compiled.put(Type.Check(Type.CHAR),Type.CHAR);
        compiled.put(Type.Check(Type.INTEGER),Type.INTEGER);
        compiled.put(Type.Check(Type.NULL),Type.NULL);
        compiled.put(Type.Check(Type.ROOT),Type.ROOT);
        compiled.put(Type.Check(Type.REFANY),Type.REFANY);
        compiled.put(Type.Check(Type.TEXT),Type.TEXT);
        compiled.put(Type.Check(Type.ERROR),Type.ERROR);
    }
    static void Compile(Type t) {
        class Visitor implements Type.Visitor<Void> {
            public Void visit(Type t) {
                assert t != Type.ERROR;
                return null;
            }
            public Void visit(Type.Enum t) { return null; }
            public Void visit(Type.Named t) {
                Compile(Type.Strip(t));
                return null;
            }
            public Void visit(Type.Object t) {
                Compile(t.parent);
                for (Value v : Scope.ToList(t.fields)) {
                    Value.Field f = Value.Field.Is(v);
                    Compile(Value.TypeOf(f));
                }
                for (Value v : Scope.ToList(t.methods)) {
                    Value.Method m = Value.Method.Is(v);
                    Compile(Value.TypeOf(m));
                }
                Vector<Temp.Label> defaults = new Vector<Temp.Label>(t.methodOffset + t.methodSize);
                GenMethodList(t, defaults);
                String vtable = target.vtable(Temp.getLabel(Type.GlobalUID(t)), defaults);
                frags.add(new Frag.Data(vtable));
                return null;
            }
            void GenMethodList(Type.Object t, Vector<Temp.Label> defaults) {
                if (t == null) return;
                GenMethodList(Type.Object.Is(t.parent), defaults);
                for (Value v : Scope.ToList(t.methods)) {
                    Value.Method m = Value.Method.Is(v);
		    if (m.value == null)
			defaults.add(m.offset, target.badPtr());
		    else
			defaults.add(m.offset, Temp.getLabel(Value.GlobalName(m.value)));
                }
            }
            public Void visit(Type.OpenArray t) {
                Compile(t.element);
                return null;
            }
            public Void visit(Type.Proc t) {
                Compile(t.result);
                for (Value v : Scope.ToList(t.formals)) {
                    Value.Formal f = Value.Formal.Is(v);
                    Compile(Value.TypeOf(f));
                }
                return null;
            }
            public Void visit(Type.Ref t) {
                Compile(t.target);
                return null;
            }
        }
        if (t == null) return;
        Type u = Type.Check(t);
        if (compiled.put(u, u) != null) return;
        t.accept(new Visitor());
    }

    static Temp.Label currentExit;

    static Exp Compile(Absyn.Stmt s) {
        class Visitor implements Absyn.Visitor<Void,Exp> {
            public Exp visit(Absyn.Type.Array t, Void _) { return null; }
            public Exp visit(Absyn.Type.Named t, Void _) { return null; }
            public Exp visit(Absyn.Type.Object t, Void _) { return null; }
            public Exp visit(Absyn.Type.Proc t, Void _) { return null; }
            public Exp visit(Absyn.Type.Ref t, Void _) { return null; }

            public Exp visit(Absyn.Decl.Field d, Void _) { return null; }
            public Exp visit(Absyn.Decl.Formal d, Void _) { return null; }
            public Exp visit(Absyn.Decl.Method d, Void _) { return null; }
            public Exp visit(Absyn.Decl.Module d, Void _) { return null; }
            public Exp visit(Absyn.Decl.Procedure d, Void _) { return null; }
            public Exp visit(Absyn.Decl.Tipe d, Void _) { return null; }
            public Exp visit(Absyn.Decl.Variable d, Void _) { return null; }

            public Exp visit(Absyn.Expr.Add e, Void _) { return null; }
            public Exp visit(Absyn.Expr.And e, Void _) { return null; }
            public Exp visit(Absyn.Expr.Call e, Void _) { return null; }
            public Exp visit(Absyn.Expr.Char e, Void _) { return null; }
            public Exp visit(Absyn.Expr.Deref e, Void _) { return null; }
            public Exp visit(Absyn.Expr.Div e, Void _) { return null; }
            public Exp visit(Absyn.Expr.Eq e, Void _) { return null; }
            public Exp visit(Absyn.Expr.Named t, Void _) { return null; }
            public Exp visit(Absyn.Expr.Or e, Void _) { return null; }
            public Exp visit(Absyn.Expr.Not e, Void _) { return null; }
            public Exp visit(Absyn.Expr.Lt e, Void _) { return null; }
            public Exp visit(Absyn.Expr.Gt e, Void _) { return null; }
            public Exp visit(Absyn.Expr.Le e, Void _) { return null; }
            public Exp visit(Absyn.Expr.Ge e, Void _) { return null; }
            public Exp visit(Absyn.Expr.Ne e, Void _) { return null; }
            public Exp visit(Absyn.Expr.Subtract e, Void _) { return null; }
            public Exp visit(Absyn.Expr.Multiply e, Void _) { return null; }
            public Exp visit(Absyn.Expr.Mod e, Void _) { return null; }
            public Exp visit(Absyn.Expr.Plus e, Void _) { return null; }
            public Exp visit(Absyn.Expr.Minus e, Void _) { return null; }
            public Exp visit(Absyn.Expr.Qualify e, Void _) { return null; }
            public Exp visit(Absyn.Expr.Subscript e, Void _) { return null; }
            public Exp visit(Absyn.Expr.Number e, Void _) { return null; }
            public Exp visit(Absyn.Expr.Text e, Void _) { return null; }
            public Exp visit(Absyn.Expr.Type e, Void _) { return null; }
            
            public Exp visit(Absyn.Stmt.Assign s, Void _) {
                Tree.Exp lhs = Compile(s.lhs).unEx();
                Tree.Exp rhs = Compile(s.rhs).unEx();
                if (Type.IsStructured(Expr.TypeCheck(s.lhs))) {
					// TODO
					return new Exp.Nx(null);
                }
                return new Exp.Nx(MOVE(lhs, rhs));
            }
            public Exp visit(Absyn.Stmt.Call s, Void _) {
                return Compile(s.expr);
            }
            public Exp visit(Absyn.Stmt.Exit s, Void _) {
				// TODO
				return new Exp.Nx(null);
            }
            public Exp visit(Absyn.Stmt.Eval s, Void _) {
                return Compile(s.expr);
            }
            public Exp visit(Absyn.Stmt.For s, Void _) {
                Tree.Exp step, limit, from;
                Tree.Exp.CONST step_val = null, limit_val = null, from_val = null;
                Temp index, to, by;
                Temp.Label top, test, down, up, exit;
                Tree.Stm stm = null;

                from = Compile(s.from).unEx();
                if (from instanceof Tree.Exp.CONST) {
                    from_val = (Tree.Exp.CONST)from;
                }
                index = new Temp();
                stm = SEQ(stm, MOVE(TEMP(index), from));

                limit = Compile(s.to).unEx();
                if (limit instanceof Tree.Exp.CONST) {
                    limit_val = (Tree.Exp.CONST)limit;
                } else {
                    to = new Temp();
                    stm = SEQ(stm, MOVE(TEMP(to), limit));
                    limit = TEMP(to);
                }

                if (s.by == null) step = CONST(1);
                else step = Compile(s.by).unEx();
                if (step instanceof Tree.Exp.CONST) {
                    step_val = (Tree.Exp.CONST)step;
                } else {
                    by = new Temp();
                    stm = SEQ(stm, MOVE(TEMP(by), step));
                    step = TEMP(by);
                }

                top = new Temp.Label();
                test = new Temp.Label();
                exit = new Temp.Label();

                Scope scope = Semant.scopes.get(s);
                Scope zz = Scope.Push(scope);
                EnterScope(scope);
                stm = SEQ(stm, InitValues(scope));
                if (from_val == null || limit_val == null || step_val == null) {
                    // we don't know all three values
                    stm = SEQ(stm, JUMP(test));
                } else if (step_val.value >= 0 && from_val.value <= limit_val.value) {
                    // we know we'll execute the loop at least once
                } else if (step_val.value <= 0 && limit_val.value <= from_val.value) {
                    // we know we'll execute the loop at least once
                } else {
                    // we won't execute the loop
                    stm = SEQ(stm, JUMP(test));
                }
                stm = SEQ(stm, LABEL(top));

                Temp.Label oldExit = currentExit;
                currentExit = exit;

                // make the user's variable equal to the counter
                Value v = Scope.ToList(scope).iterator().next();
                stm = SEQ(stm, MOVE(LoadLValue(Value.Variable.Is(v)), TEMP(index)));

                for (Absyn.Stmt stmt : s.stmts) {
                    stm = SEQ(stm, Compile(stmt).unNx());
                }

                // increment the counter
                stm = SEQ(stm, MOVE(TEMP(index), ADD(TEMP(index), step)));

                // generate the loop test
                stm = SEQ(stm, LABEL(test));
                if (step_val != null) {
                    // constant step value
                    if (step_val.value >= 0)
                        stm = SEQ(stm, BLE(TEMP(index), limit, top, exit));
                    else
                        stm = SEQ(stm, BGE(TEMP(index), limit, top, exit));
                } else {
                    // variable step value
                    up = new Temp.Label();
                    down = new Temp.Label();

                    stm = SEQ(stm, BLT(step, CONST(0), down, up));
                    stm = SEQ(stm, LABEL(up));
                    stm = SEQ(stm, BLE(TEMP(index), limit, top, exit));
                    stm = SEQ(stm, LABEL(down));
                    stm = SEQ(stm, BGE(TEMP(index), limit, top, exit));
                }

                currentExit = oldExit;
                stm = SEQ(stm, LABEL(exit));
                Scope.Pop(zz);
                return new Exp.Nx(stm);
            }
            public Exp visit(Absyn.Stmt.If s, Void _) {
				// TODO : DONE
				Tree.Stm stm = null;
				Temp.Label [] conditionLabels = new Temp.Label[s.clauses.size()];
				Temp.Label [] bodyLabels = new Temp.Label[s.clauses.size()];
				Temp.Label exit = new Temp.Label();
				
				// Initialize all labels for branching
				for(int i = 0; i < s.clauses.size(); i++)
				{
					conditionLabels[i] = new Temp.Label();
					bodyLabels[i] = new Temp.Label();
				}
				
				for(int index = 0; index < conditionLabels.length; index++)
				{
					if(index != conditionLabels.length-1)
					{
						stm = SEQ(stm, Compile(s.clauses.get(index).expr).unCx(bodyLabels[index], conditionLabels[index+1]));
					}
					else
					{
						stm = SEQ(stm, Compile(s.clauses.get(index).expr).unCx(bodyLabels[index], exit));
					}
					
					stm = SEQ(stm, LABEL(bodyLabels[index]));
					
					// Add all methods in the body of the if clause
					for (Absyn.Stmt stmt : s.clauses.get(index).stmts) {
							stm = SEQ(stm, Compile(stmt).unNx());
					}
					
					stm = SEQ(stm, JUMP(exit));
					
					if(index != conditionLabels.length-1)
					{
						stm = SEQ(stm, LABEL(conditionLabels[index+1]));
					}
					else
					{
						stm = SEQ(stm, LABEL(exit));
					}
				}
				
				return new Exp.Nx(stm);
            }
            public Exp visit(Absyn.Stmt.If.Clause c, Void _) {
                assert false;
                return null;
            }
            public Exp visit(Absyn.Stmt.Loop s, Void _) {
				// TODO : DONE
				// EQUIVALENT TO WHILE(1)
				Tree.Stm stm = null;
				
				// Initialize the label for body and exit
				Temp.Label body = new Temp.Label();
				Temp.Label exit = new Temp.Label();
				
				// Save current exit in case a break statement occurs
				Temp.Label oldExit = currentExit;
                currentExit = exit;
				
				stm = SEQ(stm, LABEL(body));
				
				// Add all methods in the body of the loop statement
				for (Absyn.Stmt stmt : s.stmts) {
						stm = SEQ(stm, Compile(stmt).unNx());
				}

				stm = SEQ(stm, JUMP(body));
				stm = SEQ(stm, LABEL(exit));
				
				// Restore old exit after leaving the body
				currentExit = oldExit;
				
				return new Exp.Nx(stm);
            }
            public Exp visit(Absyn.Stmt.Repeat s, Void _) {
				// TODO: DONE
				// EQUIVALENT TO DO-WHILE
				Tree.Stm stm = null;
				
				// Initialize the label for body and exit
				Temp.Label body = new Temp.Label();
				Temp.Label exit = new Temp.Label();
				
				// Save current exit in case a break statement occurs
				Temp.Label oldExit = currentExit;
                currentExit = exit;
				
				stm = SEQ(stm, LABEL(body));
				
				// Add all methods in the body of the loop statement
				for (Absyn.Stmt stmt : s.stmts) {
						stm = SEQ(stm, Compile(stmt).unNx());
				}

				stm = SEQ(stm, Compile(s.expr).unCx(body, exit));
				stm = SEQ(stm, LABEL(exit));
				
				// Restore old exit after leaving the body
				currentExit = oldExit;
				
				return new Exp.Nx(stm);
            }
            public Exp visit(Absyn.Stmt.Return s, Void _) {
                if (s.expr == null)
                    return new Exp.Nx(JUMP(returnLabel));
                Tree.Stm stm = SEQ(MOVE(currentFrame.RV(), Compile(s.expr).unEx()), JUMP(returnLabel));
                return new Exp.Nx(stm);
            }
            public Exp visit(Absyn.Stmt.While s, Void _) {
				// TODO: DONE
				Tree.Stm stm = null;
				
				// Initialize the labels for branching
				Temp.Label body = new Temp.Label();
				Temp.Label exit = new Temp.Label();
				
				// Save current exit in case a break statement occurs
				Temp.Label oldExit = currentExit;
                currentExit = exit;
				
				// Add conditional expression and body label to the beginning of the while statement
				stm = SEQ(stm, Compile(s.expr).unCx(body, exit));
				stm = SEQ(stm, LABEL(body));
				
				// Add all methods in the body of the while statement
				for (Absyn.Stmt stmt : s.stmts) {
						stm = SEQ(stm, Compile(stmt).unNx());
				}
				
				// Add a check at the end of the body and add an exit label after the check
				stm = SEQ(stm, Compile(s.expr).unCx(body, exit));
				stm = SEQ(stm, LABEL(exit));

				// Restore old exit after leaving the body
				currentExit = oldExit;
				return new Exp.Nx(stm);
            }
            public Exp visit(Absyn.Stmt.Block s, Void _) {
				Tree.Stm stm = null;
				// TODO
				return new Exp.Nx(stm);
            }
        }
        if (s == null) return null;
        return s.accept(new Visitor(), null);
    }

    static HashMap<Absyn.Expr,Temp> temps = new HashMap<Absyn.Expr,Temp>();
    static Temp PassObject(Absyn.Expr e) { return temps.get(e); }
    static Exp Compile(Absyn.Expr e) {
        class Visitor implements Absyn.Visitor<Void,Exp> {
            public Exp visit(Absyn.Stmt.Assign s, Void _) { return null; }
            public Exp visit(Absyn.Stmt.Call s, Void _) { return null; }
            public Exp visit(Absyn.Stmt.Exit s, Void _) { return null; }
            public Exp visit(Absyn.Stmt.Eval s, Void _) { return null; }
            public Exp visit(Absyn.Stmt.For s, Void _) { return null; }
            public Exp visit(Absyn.Stmt.If s, Void _) { return null; }
            public Exp visit(Absyn.Stmt.If.Clause s, Void _) { return null; }
            public Exp visit(Absyn.Stmt.Loop s, Void _) { return null; }
            public Exp visit(Absyn.Stmt.Repeat s, Void _) { return null; }
            public Exp visit(Absyn.Stmt.Return s, Void _) { return null; }
            public Exp visit(Absyn.Stmt.While s, Void _) { return null; }
            public Exp visit(Absyn.Stmt.Block s, Void _) { return null; }

            public Exp visit(Absyn.Type.Array t, Void _) { return null; }
            public Exp visit(Absyn.Type.Named t, Void _) { return null; }
            public Exp visit(Absyn.Type.Object t, Void _) { return null; }
            public Exp visit(Absyn.Type.Proc t, Void _) { return null; }
            public Exp visit(Absyn.Type.Ref t, Void _) { return null; }

            public Exp visit(Absyn.Decl.Field v, Void _) { return null; }
            public Exp visit(Absyn.Decl.Formal v, Void _) { return null; }
            public Exp visit(Absyn.Decl.Method v, Void _) { return null; }
            public Exp visit(Absyn.Decl.Module v, Void _) { return null; }
            public Exp visit(Absyn.Decl.Procedure v, Void _) { return null; }
            public Exp visit(Absyn.Decl.Tipe v, Void _) { return null; }
            public Exp visit(Absyn.Decl.Variable v, Void _) { return null; }

            public Exp visit(Absyn.Expr.Call ce, Void _) {
                Absyn.Expr proc = ce.expr;
                Type p_type = Expr.TypeCheck(proc);
                if (p_type == Type.FIRST || p_type == Type.LAST || p_type == Type.NUMBER) {
                    Iterator<Absyn.Expr> args = ce.actuals.iterator();
                    Absyn.Expr arg = args.next();
                    Type t = Expr.TypeCheck(arg);
                    if (Type.OpenArray.Is(t) != null) {
                        if (p_type == Type.FIRST) return new Exp.Ex(CONST(0));
                        Tree.Exp exp = Compile(arg).unEx();
                        Tree.Exp.MEM mem = (Tree.Exp.MEM)exp;
                        Tree.Exp number = MEM(mem.exp, mem.offset.value-target.wordSize());
                        if (p_type == Type.LAST)
                            return new Exp.Ex(SUB(number, CONST(1)));
                        assert p_type == Type.NUMBER;
                        return new Exp.Ex(number);
                    }
                    t = TypeExpr.Split(proc);
                    if (Type.Enum.Is(t) != null) {
                        if (p_type == Type.FIRST) return new Exp.Ex(CONST(0));
                        int number = Type.Number(t);
                        if (p_type == Type.LAST) return new Exp.Ex(CONST(number-1));
                        assert p_type == Type.NUMBER;
                        return new Exp.Ex(CONST(number));
                    }
                    assert t == Type.INTEGER;
                    assert target.wordSize() == Integer.SIZE / 8;
                    if (p_type == Type.FIRST) return new Exp.Ex(CONST(Integer.MIN_VALUE));
                    if (p_type == Type.LAST) return new Exp.Ex(CONST(Integer.MAX_VALUE));
                    assert p_type == Type.NUMBER;
                    return new Exp.Ex(CONST(Type.Number(t)));
                } else if (p_type == Type.ORD) {
                    Iterator<Absyn.Expr> args = ce.actuals.iterator();
                    return Compile(args.next());
                } else if (p_type == Type.VAL) {
                    Iterator<Absyn.Expr> args = ce.actuals.iterator();
                    Exp exp = Compile(args.next());
                    Type t = TypeExpr.Split(args.next());
                    if (Type.Enum.Is(t) != null) {
                        Temp.Label badSub = target.badSub();
                        Temp.Label okLo = new Temp.Label();
                        Temp.Label okHi = new Temp.Label();
                        Temp i = new Temp();
                        Tree.Stm loCheck = null, hiCheck = null;
                        if (badSub != null) {
                            Tree.Exp number = CONST(Type.Number(t));
                            loCheck = SEQ(BLT(TEMP(i), CONST(0), badSub, okLo), LABEL(okLo));
                            hiCheck = SEQ(BGE(TEMP(i), number, badSub, okHi), LABEL(okHi));
                        }
                        exp = new Exp.Ex(ESEQ(SEQ(MOVE(TEMP(i), exp.unEx()), loCheck, hiCheck), TEMP(i)));
                    }
                    return exp;
                } else if (p_type == Type.NEW) {
                    Iterator<Absyn.Expr> args = ce.actuals.iterator();
                    Absyn.Expr e = args.next();
                    Type t = TypeExpr.Split(e);
                    assert t != null;
                    t = Type.Check(t);
                    Compile(t);
                    Type.Ref ref = Type.Ref.Is(t);
                    if (ref != null) {
                        Type r = ref.target;
                        r = Type.Check(r);
                        if (Type.OpenArray.Is(r) != null) {
                            int n = ce.actuals.size() - 1;
                            if (n > 1) {
                                Semant.error(ce, "multi-dimensional open arrays not implemented");
                            }
                            Tree.Exp exp = Compile(args.next()).unEx();
                            Temp size = new Temp();
                            return new Exp.Ex(ESEQ(MOVE(TEMP(size), exp),
                                    CALL(NAME(Temp.getLabel("new")),
                                            Exps(MUL(TEMP(size), CONST(target.wordSize())), TEMP(size)))));
                        }
                        // simple scalar
                        return new Exp.Ex(CALL(NAME(Temp.getLabel("new")), Exps(CONST(target.wordSize()), CONST(1))));
                    }
                    Type.Object object = Type.Object.Is(t);
                    if (object != null) {
                        int size = object.fieldSize * target.wordSize();
                        Label vtable = Temp.getLabel(Type.GlobalUID(t));
                        assert vtable != null;
                        return new Exp.Ex(CALL(NAME(Temp.getLabel("new")), Exps(CONST(size), NAME(vtable))));
                    }
                    assert false;
                    return null;
                }

                if (p_type == null) p_type = QualifyExpr.MethodType(proc);
                Scope formals = Type.Proc.Is(p_type).formals;
                Tree.Exp exp = Compile(proc).unEx();
                LinkedList<Tree.Exp>args = new LinkedList<Tree.Exp>();
                Temp t = PassObject(proc);
                if (t != null) args.add(TEMP(t));
                Iterator<Absyn.Expr> actuals = ce.actuals.iterator();
                for (Value f : Scope.ToList(formals)) {
                    Value.Formal formal = Value.Formal.Is(f);
                    switch (formal.mode) {
                    case VALUE: {
                        Tree.Exp actual = Compile(actuals.next()).unEx();
                        if (Type.IsStructured(formal.type)) {
                            // we need to make a copy in the callee
                            Tree.Exp.MEM mem = (Tree.Exp.MEM)actual;
                            actual = ADD(mem.exp, mem.offset);
                        }
                        args.add(actual);
                        break;
                    }
                    case VAR: {
                        Tree.Exp actual = Compile(actuals.next()).unEx();
                        Tree.Exp.MEM mem  = (Tree.Exp.MEM)actual;
                        args.add(ADD(mem.exp, mem.offset));
                        break;
                    }
                    case READONLY: {
                        Tree.Exp actual = Compile(actuals.next()).unEx();
                        if (Type.IsStructured(formal.type)) {
                            Tree.Exp.MEM mem = (Tree.Exp.MEM)actual;
                            args.add(ADD(mem.exp, mem.offset));
                        } else if (actual instanceof Tree.Exp.MEM) {
                            Tree.Exp.MEM mem = (Tree.Exp.MEM)actual;
                            args.add(ADD(mem.exp, mem.offset));
                        } else {
                            Frame.Access access = currentFrame.allocLocal(null);
                            Tree.Exp.MEM mem = (Tree.Exp.MEM)access.exp(currentFrame);
                            args.add(ESEQ(MOVE(access.exp(currentFrame), actual), ADD(mem.exp, mem.offset)));
                        }
                        break;
                    }
                    default:
                        assert false;
                        return null;
                    }
                }
                return new Exp.Ex(CALL(exp, args.toArray(new Tree.Exp[]{})));
            }
            public Exp visit(Absyn.Expr.Or e, Void _) {
                Exp l = Compile(e.left);
                Exp r = Compile(e.right);
                return new Exp.Cx.IfThenElseExp(l, new Exp.Ex(CONST(1)), r);
            }
            public Exp visit(Absyn.Expr.And e, Void _) {
                Exp l = Compile(e.left);
                Exp r = Compile(e.right);
                return new Exp.Cx.IfThenElseExp(l, r, new Exp.Ex(CONST(0)));
            }
            public Exp visit(Absyn.Expr.Not e, Void _) {
                Exp exp = Compile(e.expr);
                return new Exp.Cx.IfThenElseExp(exp, new Exp.Ex(CONST(0)), new Exp.Ex(CONST(1)));
            }
            public Exp visit(Absyn.Expr.Lt e, Void _) {
                Exp l = Compile(e.left);
                Exp r = Compile(e.right);
                return new Exp.Cx.Rel(Tree.Stm.CJUMP.Operator.BLT, l.unEx(), r.unEx());
            }
            public Exp visit(Absyn.Expr.Gt e, Void _) {
                Exp l = Compile(e.left);
                Exp r = Compile(e.right);
                return new Exp.Cx.Rel(Tree.Stm.CJUMP.Operator.BGT, l.unEx(), r.unEx());
            }
            public Exp visit(Absyn.Expr.Le e, Void _) {
                Exp l = Compile(e.left);
                Exp r = Compile(e.right);
                return new Exp.Cx.Rel(Tree.Stm.CJUMP.Operator.BLE, l.unEx(), r.unEx());
            }
            public Exp visit(Absyn.Expr.Ge e, Void _) {
                Exp l = Compile(e.left);
                Exp r = Compile(e.right);
                return new Exp.Cx.Rel(Tree.Stm.CJUMP.Operator.BGE, l.unEx(), r.unEx());
            }
            public Exp visit(Absyn.Expr.Ne e, Void _) {
                Exp l = Compile(e.left);
                Exp r = Compile(e.right);
                return new Exp.Cx.Rel(Tree.Stm.CJUMP.Operator.BNE, l.unEx(), r.unEx());
            }
            public Exp visit(Absyn.Expr.Eq e, Void _) {
                Exp l = Compile(e.left);
                Exp r = Compile(e.right);
                return new Exp.Cx.Rel(Tree.Stm.CJUMP.Operator.BEQ, l.unEx(), r.unEx());
            }
            public Exp visit(Absyn.Expr.Add e, Void _) {
                Exp l = Compile(e.left);
                Exp r = Compile(e.right);
                return new Exp.Ex(ADD(l.unEx(), r.unEx()));
            }
            public Exp visit(Absyn.Expr.Subtract e, Void _) {
                Exp l = Compile(e.left);
                Exp r = Compile(e.right);
                return new Exp.Ex(SUB(l.unEx(), r.unEx()));
            }
            public Exp visit(Absyn.Expr.Multiply e, Void _) {
                Exp l = Compile(e.left);
                Exp r = Compile(e.right);
                return new Exp.Ex(MUL(l.unEx(), r.unEx()));
            }
            public Exp visit(Absyn.Expr.Div e, Void _) {
                Exp l = Compile(e.left);
                Exp r = Compile(e.right);
                return new Exp.Ex(DIV(l.unEx(), r.unEx()));
            }
            public Exp visit(Absyn.Expr.Mod e, Void _) {
                Exp l = Compile(e.left);
                Exp r = Compile(e.right);
                return new Exp.Ex(MOD(l.unEx(), r.unEx()));
            }
            public Exp visit(Absyn.Expr.Plus e, Void _) {
                return Compile(e.expr);
            }
            public Exp visit(Absyn.Expr.Minus e, Void _) {
                Exp exp = Compile(e.expr);
                return new Exp.Ex(SUB(CONST(0), exp.unEx()));
            }
            public Exp visit(Absyn.Expr.Deref e, Void _) {
                Tree.Exp exp = Compile(e.expr).unEx();
                Temp.Label badPtr = target.badPtr();
                Temp a = new Temp();
                Tree.Stm nullCheck = null;
                if (badPtr != null) {
                    Temp.Label okPtr = new Temp.Label();
                    nullCheck = SEQ(BEQ(TEMP(a), CONST(0), badPtr, okPtr), LABEL(okPtr));
                }
                exp = MEM(ESEQ(SEQ(MOVE(TEMP(a), exp), nullCheck), TEMP(a)));
                return new Exp.Ex(exp);
            }
            public Exp visit(Absyn.Expr.Qualify e, Void _) {
                Type t = Expr.TypeCheck(e.expr);
                Value v = QualifyExpr.Split(e);
                assert v != null;
                // TODO: object fields/methods, object type methods, module values
                return new Exp.Ex(Load(v));
            }
            public Exp visit(Absyn.Expr.Subscript e, Void _) {
				Tree.Exp exp = null;
				// TODO
				return new Exp.Ex(exp);
            }
            public Exp visit(Absyn.Expr.Named e, Void _) {
                Value v = NamedExpr.Split(e);
                return new Exp.Ex(Load(v));
            }
            public Exp visit(Absyn.Expr.Number e, Void _) {
                String[] split = e.token.image.split("_");
                if (split.length == 1)
                    return new Exp.Ex(CONST(Integer.parseInt(split[0])));
                else {
				    // TODO
				    assert split.length == 2;
				    return new Exp.Ex(null);
                }
            }
            public Exp visit(Absyn.Expr.Char e, Void _) {
				// TODO
				return new Exp.Ex(null);
            }
            public Exp visit(Absyn.Expr.Text e, Void _) {
                return new Exp.Ex(NAME(stringLabel(mapString(e.token.image))));
            }
            public Exp visit(Absyn.Expr.Type e, Void _) { assert false; return null; }
        }
        if (e == null) return null;
        assert Expr.types.containsKey(e);
        return e.accept(new Visitor(), null);
    }

    static HashMap<String,Temp.Label> strings = new HashMap<String,Temp.Label>();
    static String mapString(String s) {
        String result = "";
        int i = 0;
        char c;
        if ((c = s.charAt(i++)) != '"')
            throw new Error();
        while ((c = s.charAt(i++)) != '"') {
            if (c == '\\')
                switch (c = s.charAt(i++)) {
                case 'b':
                    result += '\b';
                    break;
                case 't':
                    result += '\t';
                    break;
                case 'n':
                    result += '\n';
                    break;
                case 'f':
                    result += '\f';
                    break;
                case 'r':
                    result += '\r';
                    break;
                case '\'':
                    result += '\'';
                    break;
                case '"':
                    result += '\"';
                    break;
                case '\\':
                    result += '\\';
                    break;
                default:
                    int value = c - '0';
                    c = s.charAt(i);
                    if (c >= '0' && c <= '7') {
                        i++;
                        value <<= 3;
                        value += c - '0';
                        c = s.charAt(i);
                        if (c >= '0' && c <= '7') {
                            i++;
                            value <<= 3;
                            value += c - '0';
                        }
                    }
                    result += (char) value;
                    break;
                }
            else
                result += c;
        }
        return result;
    }

    static Temp.Label stringLabel(String s) {
        Temp.Label l = strings.get(s);
        if (l != null)
            return l;
        l = new Temp.Label();
        strings.put(s, l);
        frags.add(new Frag.Data(target.string(l, s)));
        return l;
    }
}
