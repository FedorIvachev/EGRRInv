###################################################################
EGRR := module ()

    description     "a package implementing a family of EG and RR algorithms";
    option package;
    export
        EG,
        RR,
        InvRR,
        InvR,
        InvRRmodOld,
        InvRRmod,
        TriangleEG,
        TriangleRR;
    local
        alpha,
        pin,
        dualnormal,
        DiffRow,
        diff_row,
        diff_row_nr,
        dep;

    global
        DiffCount,
        AlgCount;

    dep := proc (M0)
        local M, n, DM, k, ndx, i, j;

        M := copy(M0);
        n := LinearAlgebra:-RowDimension(M);
        DM := Matrix(n, n, 0);
        for k to n do
            DM[k, k] := 1
        end do;
        ndx := {seq(k, k = 1 .. n)};
        for i to n do
            for j in ndx do
                if M[j, i] <> 0 then
                    ndx := ndx minus {j};
                    for k in ndx do
                        if M[k, i] <> 0 then
                            DM[k, 1 .. n] := LinearAlgebra:-Map(normal, -(M[k, i]*DM[j, 1 .. n])/M[j, i]+DM[k, 1 .. n], expanded);
                            M[k, 1 .. n] := LinearAlgebra:-Map(normal, -(M[k, i]*M[j, 1 .. n])/M[j, i]+M[k, 1 .. n], expanded);
                            AlgCount := AlgCount + n*6;
                        end if
                    end do;
                    break
                end if
            end do
        end do;
        if 0 < nops(ndx) then
            return DM[ndx[1], 1 .. n]
        else
            return false
        end if;
    end proc;

    dualnormal := e->simplify(radnormal(e),RootOf);

    DiffRow := proc (rw, r, x, n, cd, remember)
        if remember then
            diff_row(convert(rw, list), r, x, n, cd);
        else
            diff_row_nr(convert(rw, list), r, x, n, cd);
        end if;
    end proc;

    diff_row := proc (rw, r, x, n, cd)
    option remember;
        local
            dummy, V;

        if r <= 0 then
           Vector[row](rw);
        elif r>1 then
           diff_row(convert(diff_row(rw, r-1, x, n, cd), list), 1, x, n, cd);
        else
           DiffCount := DiffCount + cd;
           AlgCount := AlgCount + cd;
           dummy := Vector[row](cd, 0);
           V := Vector[row](rw);
           dummy[1 .. cd-n] := Vector[row](V[n+1 .. cd]);
           eval(map(dualnormal,dummy+LinearAlgebra:-Map(z->diff(z, x), V)));
         end if;
    end proc;

    diff_row_nr := proc (rw, r, x, n, cd)
        local
            dummy, V;

        if r <= 0 then
           Vector[row](rw);
        elif r>1 then
           procname(convert(procname(rw, r-1, x, n, cd), list), 1, x, n, cd);
        else
           DiffCount := DiffCount + cd;
           AlgCount := AlgCount + cd;
           dummy := Vector[row](cd, 0);
           V := Vector[row](rw);
           dummy[1 .. cd-n] := Vector[row](V[n+1 .. cd]);
           eval(map(dualnormal,dummy+LinearAlgebra:-Map(z->diff(z, x), V)));
         end if;
    end proc;

    alpha := proc (rw, n, cd)
        local
            i;

        for i to cd while rw[i] = 0 do end do;
        floor((cd-i)/n)+1
    end proc;

    pin := proc (rw, start, n)
        local
            i;

        for i to n while rw[start+i] = 0 do end do;
        `if`(i<=n,i,0);
    end proc;

    EG := proc(EM1::Matrix, m, x, remember::boolean:=false, noLA::boolean:=false)
        local
            rd, cd, n, RM, ns, p, dummy, i, shifts, r, d, EM;

        forget(diff_row);
        DiffCount := 0;
        AlgCount := 0;
        EM := copy(EM1);
        rd := LinearAlgebra:-RowDimension(EM);
        cd := LinearAlgebra:-ColumnDimension(EM);
        n := cd/m;
        shifts := 0;
        while shifts<cd+1 do
            RM := LinearAlgebra:-SubMatrix(EM, 1 .. rd, 1 .. n);
            if noLA then
                p := dep(RM);
                if p=false then
                    break;
                end if;
            else
                ns := LinearAlgebra:-NullSpace(LinearAlgebra:-Transpose(RM));
                if nops(ns)=0 then
                    break;
                end if;
                p := LinearAlgebra:-Transpose(ns[1]);
            end if;
            for i to rd while p[i] = 0 do end do;
            p := map(z->z/p[i],p);
            AlgCount := AlgCount + rd;
            dummy := LinearAlgebra:-Map(dualnormal, LinearAlgebra:-VectorMatrixMultiply(p, EM));
            AlgCount := AlgCount + cd*(2*rd-1);
            d := alpha(dummy, n, cd);
            if d=0 then
                shifts := cd+1;
                break
            end if;
            r := m-d;
            shifts := shifts + r;
            EM[i] := DiffRow(eval(dummy), r, x, n, cd, remember);
        end do;
        eval(EM), evalb(shifts<cd+1);
    end proc;

    TriangleEG := proc(EM1::Matrix, m, x, remember::boolean:=false)
        local
            rd, cd, n, dummy, i, j, k, pinrows, shifts, r, d, EM;

        forget(diff_row);
        DiffCount := 0;
        AlgCount := 0;
        EM := copy(EM1);
        rd := LinearAlgebra:-RowDimension(EM);
        cd := LinearAlgebra:-ColumnDimension(EM);
        n := cd/m;
        pinrows := Array(0..n,fill={});
        for i to rd do
            d := pin(EM[i], 0, n);
            pinrows[d] := pinrows[d] union {i};
        end do;
        shifts := 0;
        while shifts<cd+1 do
            if pinrows[0]<>{} then
                i := pinrows[0][1];
                pinrows[0] := pinrows[0] minus {i};
                d := alpha(EM[i], n, cd);
                if d=0 then
                    shifts := cd+1;
                else
                    r := m-d;
                    shifts := shifts + r;
                    EM[i] := DiffRow(eval(EM[i]), r, x, n, cd, remember);
                    d := pin(EM[i], 0, n);
                    pinrows[d] := pinrows[d] union {i};
                end if;
            else
                for k to n do
                    if nops(pinrows[k])>1 then
                        i := pinrows[k][2];
                        j := pinrows[k][1];
                        pinrows[k] := pinrows[k] minus {i};
                        dummy := LinearAlgebra:-Map(dualnormal, EM[i]-EM[i,k]*EM[j]/EM[j,k]);
                        AlgCount := AlgCount + cd*3;
                        d := pin(dummy, 0, n);
                        if d=0 then
                            d := alpha(dummy, n, cd);
                            if d=0 then
                                shifts := cd+1;
                            else
                                r := m-d;
                                shifts := shifts + r;
                                EM[i] := DiffRow(eval(dummy), r, x, n, cd, remember);
                                d := pin(EM[i], 0, n);
                                pinrows[d] := pinrows[d] union {i};
                            end if;
                        else
                            EM[i] := dummy;
                            pinrows[d] := pinrows[d] union {i};
                        end if;
                        break;
                     end if;
                end do;
                if k>n then
                    break;
                end if;
            end if;
        end do;
        eval(EM), evalb(shifts<cd+1);
    end proc;

    RR := proc(EM1::Matrix, m, x, remember::boolean:=false, noLA::boolean:=false)
        local
            rd, cd, n, RM, ns, p, dummy, i, j, alphai, alphas, d, EM, time_start, time_finish, steps;
        time_start := time();
        steps := 0;
        forget(diff_row);
        DiffCount := 0;
        AlgCount := 0;
        EM := copy(EM1);
        rd := LinearAlgebra:-RowDimension(EM);
        cd := LinearAlgebra:-ColumnDimension(EM);
        n := cd/m;
        alphas := [seq(alpha(EM[i], n, cd), i = 1..rd)];
        alphai := min(op(alphas));
        while alphai>0 do
            RM := Matrix([seq([EM[i,cd-alphas[i]*n+1..cd-alphas[i]*n+n]], i = 1 .. rd)]);
            if noLA then
                p := dep(RM);
                if p=false then
                    break;
                end if;
            else
                ns := LinearAlgebra:-NullSpace(LinearAlgebra:-Transpose(RM));
                if nops(ns)=0 then
                    break;
                end if;
                p := LinearAlgebra:-Transpose(ns[1]);
            end if;
            alphai :=0;
            for j to rd do
                if (p[j] <> 0) and (alphas[j]>alphai) then
                    alphai := alphas[j];
                    i := j;
                end if
            end do;
            p := map(z->z/p[i],p);
            AlgCount := AlgCount + rd;
            dummy := LinearAlgebra:-Map(dualnormal, LinearAlgebra:-VectorMatrixMultiply(p,
                                    Matrix([seq([`if`(p[j] = 0, EM[j], DiffRow(eval(EM[j]), alphai-alphas[j], x, n, cd, remember))], j = 1 .. rd)])));
            AlgCount := AlgCount + cd*(2*rd-1);
            EM[i] := dummy;
            alphai := alpha(dummy, n, cd);
            alphas[i] := alphai;
            steps := steps + 1;
        end do;
        time_finish := time();

        eval(EM), evalb(alphai>0), eval(time_finish - time_start), steps;
    end proc;

    InvRR := proc(EM1::Matrix, m, x, remember::boolean:=false, noLA::boolean:=false)
        local
            rd, cd, n, RM, ns, p, dummy, i, j, alphai, alphas, d, EM, W, dummy2, k, Linv, time_start, time_finish;

        time_start := time();
        forget(diff_row);
        DiffCount := 0;
        AlgCount := 0;
        EM := copy(EM1);
        rd := LinearAlgebra:-RowDimension(EM);
        cd := LinearAlgebra:-ColumnDimension(EM);
        n := cd/m;
        #print('alphas\n');
        alphas := [seq(alpha(EM[i], n, cd), i = 1..rd)];
        alphai := min(op(alphas));
        W := Matrix(rd, cd);
        for j to rd do
            W[j, cd-rd+j] := 1;
        end do;
        while alphai>0 do
            RM := Matrix([seq([EM[i,cd-alphas[i]*n+1..cd-alphas[i]*n+n]], i = 1 .. rd)]);
            #print('RM ', RM);
            if noLA then
                p := dep(RM);
                if p=false then
                    break;
                end if;
            else
                ns := LinearAlgebra:-NullSpace(LinearAlgebra:-Transpose(RM));
                if nops(ns)=0 then
                    break;
                end if;
                p := LinearAlgebra:-Transpose(ns[1]);
            end if;
            alphai :=0;
            for j to rd do
                if (p[j] <> 0) and (alphas[j]>alphai) then
                    alphai := alphas[j];
                    i := j;
                end if
            end do;
            p := map(z->z/p[i],p);
            #print('p ', p);
            AlgCount := AlgCount + rd;
            dummy := LinearAlgebra:-Map(dualnormal, LinearAlgebra:-VectorMatrixMultiply(p,
                                    Matrix([seq([`if`(p[j] = 0, EM[j], DiffRow(eval(EM[j]), alphai-alphas[j], x, n, cd, remember))], j = 1 .. rd)])));
            dummy2 := LinearAlgebra:-Map(dualnormal, LinearAlgebra:-VectorMatrixMultiply(p,
                                    Matrix([seq([`if`(p[j] = 0, W[j], DiffRow(eval(W[j]), alphai-alphas[j], x, n, cd, remember))], j = 1 .. rd)])));
            W[i] := dummy2;
            AlgCount := AlgCount + cd*(2*rd-1);
            EM[i] := dummy;
            alphai := alpha(dummy, n, cd);
            alphas[i] := alphai;
            #print('W ', W);
            #print('Em', EM);
        end do;
        Linv := Matrix(rd, rd);
        for j to rd do
            for k to rd do
                Linv[j, k] := EM[j, cd - rd + k];
            end do;
        end do;
        Linv := LinearAlgebra:-Multiply(LinearAlgebra:-MatrixInverse(Linv), W);

        time_finish := time();
        eval(Linv), eval(EM), evalb(alphai>0), eval(time_finish - time_start);
    end proc;

    InvR := proc(L0::Matrix, m, x, 
        remember::boolean:=false)
        local
            rd, cd, n, L1, alphas, alphai, W, Lf, i, j, ns, p, num, dummy, dummy2, t1, t2, L;
        L := Matrix(2, 4);
        for i to 2 do
            for j to 4 do
                L[i,j] := randpoly(x, coeffs = rand(-1..1), expons = rand(0..1));
            end do;
        end do;
        print('L ', L);
        t1 := time();
        forget(diff_row);
        DiffCount := 0;
        AlgCount := 0;
        #print('invR\n');
        L1 := copy(L);
        rd := LinearAlgebra:-RowDimension(L1);
        cd := LinearAlgebra:-ColumnDimension(L1);
        n := cd/m;
        alphas := [seq(alpha(L1[i], n, cd), i = 1..rd)];
        #print('alphas ', alphas);
        alphai := min(op(alphas));
        W := Matrix([seq([seq(eval(verify(i + cd - rd, j), [true=1,false=0]), j = 1..cd)], i = 1..rd)]);

        while alphai>0 do
            Lf := Matrix([seq([L1[i,cd-alphas[i]*n+1..cd-alphas[i]*n+n]], i = 1 .. rd)]);
            #print('Lf ', Lf);
            ns := LinearAlgebra:-NullSpace(LinearAlgebra:-Transpose(Lf));
            if nops(ns)=0 then
                break;
            end if;
            p := LinearAlgebra:-Transpose(ns[1]);
            alphai :=0;
            for i to rd do
                if (p[i] <> 0) and (alphas[i]>alphai) then
                    alphai := alphas[i];
                    num := i;
                end if
            end do;
            p := map(z->z/p[num],p);
            AlgCount := AlgCount + rd;
            dummy := LinearAlgebra:-Map(dualnormal, LinearAlgebra:-VectorMatrixMultiply(p,
                                    Matrix([seq([`if`(p[j] = 0, L1[j], DiffRow(eval(L1[j]), alphai-alphas[j], x, n, cd, remember))], j = 1 .. rd)])));
            dummy2 := LinearAlgebra:-Map(dualnormal, LinearAlgebra:-VectorMatrixMultiply(p,
                                    Matrix([seq([`if`(p[j] = 0, W[j], DiffRow(eval(W[j]), alphai-alphas[j], x, n, cd, remember))], j = 1 .. rd)])));
            W[num] := dummy2;
            AlgCount := AlgCount + cd*(2*rd-1);
            L1[num] := dummy;
            alphai := alpha(dummy, n, cd);
            alphas[num] := alphai;
            print('W ', W);

        end do;
        
        t2 := time();


        eval(t2-t1), eval(L1), eval(W);
    end proc;


    InvRRmodOld := proc(EM1::Matrix, m, x, remember::boolean:=false)
        local
            rd, cd, n, RM, ns, p, dummy, i, j, alphai, alphas, d, EM, W, dummy2, k, Linv, time_start, time_finish, st, p_prev, alphas_prev, i_prev, alphai_prev, diff_row, diff_help, steps;
        time_start := time();
        forget(diff_row);
        DiffCount := 0;
        AlgCount := 0;
        st := 1;
        EM := copy(EM1);
        rd := LinearAlgebra:-RowDimension(EM);
        cd := LinearAlgebra:-ColumnDimension(EM);
        n := cd/m;
        alphas := [seq(alpha(EM[i], n, cd), i = 1..rd)];
        alphai := min(op(alphas));
        W := Matrix([seq([seq(eval(verify(i + cd - rd, j), [true=1,false=0]), j = 1..cd)], i = 1..rd)]);
        steps := 0;
        while alphai>0 do
            if (st <> 0) then 
                st := 0;
            else 
                st := 1;
            end if;
            #print('st ', st);
            RM := Matrix([seq([EM[i,cd-alphas[i]*n+1..cd-alphas[i]*n+n]], i = 1 .. rd)]);
            #print('RM ', RM);
            ns := LinearAlgebra:-NullSpace(LinearAlgebra:-Transpose(RM));
            if nops(ns)=0 then
                break;
            end if;
            p := LinearAlgebra:-Transpose(ns[1]);
            alphai :=0;
            for j to rd do
                if (p[j] <> 0) and (alphas[j]>alphai) then
                    alphai := alphas[j];
                    i := j;
                end if
            end do;
            p := map(z->z/p[i],p);
            #print('p ', p);
            #print('al ', alphas);
            AlgCount := AlgCount + rd;
            dummy := LinearAlgebra:-Map(dualnormal, LinearAlgebra:-VectorMatrixMultiply(p,
                                    Matrix([seq([`if`(p[j] = 0, EM[j], DiffRow(eval(EM[j]), alphai-alphas[j], x, n, cd, remember))], j = 1 .. rd)])));
            dummy2 := Vector[row](cd);
            if (st <> 0) then
                if (i_prev <> i) then
                    #print('here1');
                    dummy2 := LinearAlgebra:-Map(dualnormal, LinearAlgebra:-VectorMatrixMultiply(p_prev,
                                Matrix([seq([`if`(p_prev[j] = 0, W[j], DiffRow(eval(W[j]), alphai_prev-alphas_prev[j], x, n, cd, remember))], j = 1 .. rd)])));
                    W[i_prev] := dummy2;
                    dummy2 := LinearAlgebra:-Map(dualnormal, LinearAlgebra:-VectorMatrixMultiply(p,
                                   Matrix([seq([`if`(p[j] = 0, W[j], DiffRow(eval(W[j]), alphai-alphas[j], x, n, cd, remember))], j = 1 .. rd)])));
                else
                    for j to rd do
                        if (i = j) then
                            diff_row := p[i] * p_prev[i] * W[i];
                            dummy2 = dummy2 + diff_row;
                        else
                            if (alphas[i] - alphas[j] < alphas_prev[i] - alphas_prev[j]) then
                                if (p[j] <> 0) then
                                    diff_row := (DiffRow(eval(W[j]), alphai-alphas[j], x, n, cd, remember));
                                    diff_help := p[i] * p_prev[j] * (DiffRow(eval(diff_row), alphas_prev[i] - alphas_prev[j] - alphai + alphas[j], x, n, cd, remember));
                                    dummy2 := dummy2 + p[j] * diff_row + diff_help;
                                    #print('1 ', dummy2);
                                else
                                    diff_help := p[i] * p_prev[j] * (DiffRow(eval(W[j]), alphas_prev[i] - alphas_prev[j] - alphai + alphas[j], x, n, cd, remember));
                                    dummy2 := dummy2 + diff_help;
                                    #print('2 ', diff_row);
                                end if;
                                #print(dummy2);
                            else
                                if (p_prev[j] <> 0) then
                                    diff_row := (DiffRow(eval(W[j]), alphas_prev[i] - alphas_prev[j], x, n, cd, remember));
                                    diff_help := p[j] * (DiffRow(eval(diff_row), alphai - alphas[j] - alphas_prev[i] + alphas_prev[j], x, n, cd, remember));
                                    dummy2 := dummy2 + p_prev[j] * p[i] * diff_row + diff_help;
                                    #print('3 ');
                                else
                                    diff_help := p[j] * (DiffRow(eval(diff_row), alphai - alphas[j] - alphas_prev[i] + alphas_prev[j], x, n, cd, remember));
                                    dummy2 := dummy2 + diff_help;
                                    #print('4 ', diff_row);
                                end if;
                                #print(dummy2);
                            end if;
                        end if;
                    end do;
                end if;
                W[i] := dummy2;
            else
                #print('here2 ');
                p_prev := p;
                alphas_prev := alphas;
                i_prev := i;
                alphai_prev := alphai;
            end if;
            #dummy2 := LinearAlgebra:-Map(dualnormal, LinearAlgebra:-VectorMatrixMultiply(p,
            #                        Matrix([seq([`if`(p[j] = 0, W[j], DiffRow(eval(W[j]), alphai-alphas[j], x, n, cd, remember))], j = 1 .. rd)])));
            #print(dummy2);
            #print('W ', W);
            AlgCount := AlgCount + cd*(2*rd-1);
            EM[i] := dummy;
            alphai := alpha(dummy, n, cd);
            alphas[i] := alphai;
            #print('Em', EM);
            steps := steps + 1;
        end do;
        alphas := [seq(alpha(EM[i], n, cd), i = 1..rd)];
        alphai := min(op(alphas));
        if (alphai = 1) then
            if (st <> 0) then
                #print(p_prev, alphas_prev, alphai_prev, i_prev);
                dummy2 := LinearAlgebra:-Map(dualnormal, LinearAlgebra:-VectorMatrixMultiply(p_prev,
                                   Matrix([seq([`if`(p_prev[j] = 0, W[j], DiffRow(eval(W[j]), alphai_prev-alphas_prev[j], x, n, cd, remember))], j = 1 .. rd)])));
                W[i_prev] := dummy2;
                #print(W[i_prev]);
            end if;
            Linv := Matrix(rd, rd);
            for j to rd do
                for k to rd do
                    Linv[j, k] := EM[j, cd - rd + k];
                end do;
            end do;
            Linv := LinearAlgebra:-Multiply(LinearAlgebra:-MatrixInverse(Linv), W);
        else 
            Linv := Matrix(1,1);
        end if;
        time_finish := time();
        eval(Linv), eval(EM), eval(W), evalb(alphai>0), eval(time_finish - time_start), eval(steps);
    end proc;


    InvRRmod := proc(EM1::Matrix, m, x, remember::boolean:=false)
        local
            rd, cd, n, RM, ns, p, dummy, i, j, alphai, alphas, d, EM, W, dummy2, k, Linv, time_start, time_finish, st, p_prev, alphas_prev, i_prev, alphai_prev, diff_row, diff_help;
        time_start := time();
        forget(diff_row);
        DiffCount := 0;
        AlgCount := 0;
        st := 1;
        EM := copy(EM1);
        rd := LinearAlgebra:-RowDimension(EM);
        cd := LinearAlgebra:-ColumnDimension(EM);
        n := cd/m;
        alphas := [seq(alpha(EM[i], n, cd), i = 1..rd)];
        alphai := min(op(alphas));
        W := Matrix([seq([seq(eval(verify(i + cd - rd, j), [true=1,false=0]), j = 1..cd)], i = 1..rd)]);

        while alphai>0 do
            if (st <> 0) then 
                st := 0;
            else 
                st := 1;
            end if;
            #print('st ', st);
            RM := Matrix([seq([EM[i,cd-alphas[i]*n+1..cd-alphas[i]*n+n]], i = 1 .. rd)]);
            #print('RM ', RM);
            ns := LinearAlgebra:-NullSpace(LinearAlgebra:-Transpose(RM));
            if nops(ns)=0 then
                break;
            end if;
            p := LinearAlgebra:-Transpose(ns[1]);
            alphai :=0;
            for j to rd do
                if (p[j] <> 0) and (alphas[j]>alphai) then
                    alphai := alphas[j];
                    i := j;
                end if
            end do;
            p := map(z->z/p[i],p);
            #print('p ', p);
            #print('al ', alphas);
            AlgCount := AlgCount + rd;
            dummy := LinearAlgebra:-Map(dualnormal, LinearAlgebra:-VectorMatrixMultiply(p,
                                    Matrix([seq([`if`(p[j] = 0, EM[j], DiffRow(eval(EM[j]), alphai-alphas[j], x, n, cd, remember))], j = 1 .. rd)])));
            dummy2 := Vector[row](cd);
            if (st <> 0) then
                for j to rd do
                    if (j = i_prev) then
                        diff_row := p[i_prev] * (DiffRow(eval(p_prev[i_prev] * W[i_prev]), alphai-alphas[i_prev], x, n, cd, remember));
                        dummy2 = dummy2 + diff_row;
                    else
                        if (alphas[i] - alphas[j] < alphas_prev[i_prev] - alphas_prev[j]) then
                            if (p[j] <> 0) then
                                diff_row := (DiffRow(eval(W[j]), alphai-alphas[j], x, n, cd, remember));
                                diff_help := p_prev[j] * (DiffRow(eval(diff_row), alphas_prev[i_prev] - alphas_prev[j] - alphai + alphas[j], x, n, cd, remember));
                                diff_help := p[i_prev] * (DiffRow(eval(diff_help), alphai - alphas[i_prev], x, n, cd, remember));
                                dummy2 := dummy2 + p[j] * diff_row + diff_help;
                                #print('1 ', dummy2);
                            else
                                diff_help := p_prev[j] * (DiffRow(eval(W[j]), alphas_prev[i_prev] - alphas_prev[j], x, n, cd, remember));
                                diff_help := p[i_prev] * (DiffRow(eval(diff_help), alphai - alphas[i_prev], x, n, cd, remember));
                                dummy2 := dummy2 + diff_help;
                                #print('2 ', diff_row);
                            end if;
                            #print(dummy2);
                        else
                            if (p_prev[j] <> 0) then
                                diff_row := (DiffRow(eval(W[j]), alphas_prev[i_prev]-alphas_prev[j], x, n, cd, remember));
                                diff_help := p[j] * (DiffRow(eval(diff_row), alphai - alphas[j] - alphas_prev[i_prev] + alphas_prev[j], x, n, cd, remember));
                                diff_row := p[i_prev] * (DiffRow(eval(p_prev[j] * diff_row), alphai - alphas[i_prev], x, n, cd, remember));
                                dummy2 := dummy2 + diff_row + diff_help;

                                #print('3 ');
                            else
                                diff_help := p[j] * (DiffRow(eval(W[j]), alphai - alphas[j], x, n, cd, remember));
                                dummy2 := dummy2 + diff_help;
                                #print('4 ');
                            end if;
                            #print(dummy2);
                        end if;
                    end if;
                end do;
                W[i] := dummy2;
            else
                #print('here2 ');
                p_prev := p;
                alphas_prev := alphas;
                i_prev := i;
                alphai_prev := alphai;
            end if;
            #dummy2 := LinearAlgebra:-Map(dualnormal, LinearAlgebra:-VectorMatrixMultiply(p,
            #                        Matrix([seq([`if`(p[j] = 0, W[j], DiffRow(eval(W[j]), alphai-alphas[j], x, n, cd, remember))], j = 1 .. rd)])));
            #W[i] := dummy2;
            AlgCount := AlgCount + cd*(2*rd-1);
            EM[i] := dummy;
            alphai := alpha(dummy, n, cd);
            alphas[i] := alphai;
            #print('Em', EM);
            #print('W ', W);
        end do;
        alphas := [seq(alpha(EM[i], n, cd), i = 1..rd)];
        alphai := min(op(alphas));
        if (alphai = 1) then
            if (st <> 0) then
                #print(p_prev, alphas_prev, alphai_prev, i_prev);
                dummy2 := LinearAlgebra:-Map(dualnormal, LinearAlgebra:-VectorMatrixMultiply(p_prev,
                                   Matrix([seq([`if`(p_prev[j] = 0, W[j], DiffRow(eval(W[j]), alphai_prev-alphas_prev[j], x, n, cd, remember))], j = 1 .. rd)])));
                W[i_prev] := dummy2;
                #print(W[i_prev]);
            end if;
            Linv := Matrix(rd, rd);
            for j to rd do
                for k to rd do
                    Linv[j, k] := EM[j, cd - rd + k];
                end do;
            end do;
            Linv := LinearAlgebra:-Multiply(LinearAlgebra:-MatrixInverse(Linv), W);
        else 
            Linv := Matrix(1,1);
        end if;
        time_finish := time();
        eval(Linv), eval(EM), eval(W), evalb(alphai>0), eval(time_finish - time_start);
    end proc;




    TriangleRR := proc(EM1::Matrix, m, x, remember::boolean:=false)
        local
            rd, cd, n, dummy, i, j, k, pinrows, alphai, alphas, d, EM;

        forget(diff_row);
        DiffCount := 0;
        AlgCount := 0;
        EM := copy(EM1);
        rd := LinearAlgebra:-RowDimension(EM);
        cd := LinearAlgebra:-ColumnDimension(EM);
        n := cd/m;
        alphas := [seq(alpha(EM[i], n, cd), i = 1..rd)];
        alphai := min(op(alphas));
        pinrows := Array(0..n,fill={});
        if alphai>0 then
            for i to rd do
                d := pin(EM[i], (m-alphas[i])*n, n);
                pinrows[d] := pinrows[d] union {i};
            end do;
        end if;
        while alphai>0 do
            if pinrows[0]<>{} then
                alphai := 0;
                break;
            else
                for k to n do
                    if nops(pinrows[k])>1 then
                        i := pinrows[k][2];
                        j := pinrows[k][1];
                        if alphas[i]<alphas[j] then
                            i,j := j,i;
                        end if;
                        pinrows[k] := pinrows[k] minus {i};
                        dummy := LinearAlgebra:-Map(dualnormal, EM[i]-EM[i,(m-alphas[i])*n+k]*DiffRow(eval(EM[j]),alphas[i]-alphas[j],x,n,cd,remember)/EM[j,(m-alphas[j])*n+k]);
                        AlgCount := AlgCount + cd*3;
                        alphai := alpha(dummy, n, cd);
                        alphas[i] := alphai;
                        if alphai>0 then
                            d := pin(dummy, (m-alphai)*n, n);
                            pinrows[d] := pinrows[d] union {i};
                        end if;
                        EM[i] := dummy;
                        break;
                    end if;
                end do;
                if k>n then
                    break;
                end if;
            end if;
        end do;
        eval(EM), evalb(alphai>0);
    end proc;


################################################################################

end module:
