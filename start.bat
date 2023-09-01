@ECHO OFF
START http://localhost:8000/index.html
C:\ProgramData\Anaconda3\python -m http.server
rem http-server -p 8000
