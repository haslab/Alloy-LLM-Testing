FROM ollama/ollama:latest

ENV OLLAMA_HOST=0.0.0.0:11434

EXPOSE 11434

RUN ollama serve & sleep 2 && ollama pull llama3.1:8b