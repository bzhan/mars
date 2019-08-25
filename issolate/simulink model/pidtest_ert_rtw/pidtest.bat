set MATLAB=E:\Program Files\MATLAB\R2014

cd .

if "%1"=="" (E:\PROGRA~2\MATLAB\R2014\bin\win64\gmake -f pidtest.mk all) else (E:\PROGRA~2\MATLAB\R2014\bin\win64\gmake -f pidtest.mk %1)
@if errorlevel 1 goto error_exit

exit /B 0

:error_exit
echo The make command returned an error of %errorlevel%
An_error_occurred_during_the_call_to_make
