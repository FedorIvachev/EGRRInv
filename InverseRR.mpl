###################################################################
EGRR := module ()

    description     "a package implementing a family of EG and RR algorithms";
    option package;
    export
        EG,
        RR,
        InvRR,
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
            rd, cd, n, RM, ns, p, dummy, i, j, alphai, alphas, d, EM;

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
        end do;
        eval(EM), evalb(alphai>0);
    end proc;

    InvRR := proc(EM1::Matrix, m, x, remember::boolean:=false, noLA::boolean:=false)
        local
            rd, cd, n, RM, ns, p, dummy, i, j, alphai, alphas, d, EM, W, dummy2, k, Linv;

        forget(diff_row);
        DiffCount := 0;
        AlgCount := 0;
        EM := copy(EM1);
        rd := LinearAlgebra:-RowDimension(EM);
        cd := LinearAlgebra:-ColumnDimension(EM);
        n := cd/m;
        alphas := [seq(alpha(EM[i], n, cd), i = 1..rd)];
        alphai := min(op(alphas));
        W := Matrix(rd, cd);
        for j to rd do
            W[j, cd-rd+j] := 1;
        end do;
        while alphai>0 do
            RM := Matrix([seq([EM[i,cd-alphas[i]*n+1..cd-alphas[i]*n+n]], i = 1 .. rd)]);
            #print("RM: ", RM);
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
            dummy2 := LinearAlgebra:-Map(dualnormal, LinearAlgebra:-VectorMatrixMultiply(p,
                                    Matrix([seq([`if`(p[j] = 0, W[j], DiffRow(eval(W[j]), alphai-alphas[j], x, n, cd, remember))], j = 1 .. rd)])));
            W[i] := dummy2;
            AlgCount := AlgCount + cd*(2*rd-1);
            EM[i] := dummy;
            alphai := alpha(dummy, n, cd);
            alphas[i] := alphai;
            print(W);
        end do;
        Linv := Matrix(rd, rd);
        for j to rd do
            for k to rd do
                Linv[j, k] := EM[j, cd - rd + k];
            end do;
        end do;
        Linv := LinearAlgebra:-Multiply(LinearAlgebra:-MatrixInverse(Linv), W);
        eval(Linv), eval(EM), evalb(alphai>0);
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
        eval(EM), evalb(alTTTphai>0);
    end proc;


################################################################################

end module:
