const express = require("express"),
    app = express(),
    cors = require("cors"),
    bodyParser = require("body-parser"),
    path = require("path"),
    sdk = require("vuetify-file-browser-server/sdk");

// enable CORS
app.use(cors());

// parse incoming request body
app.use(bodyParser.urlencoded({ extended: true }));
app.use(bodyParser.json());

// get AWS configuration from process.env
const { AWS_ACCESS_KEY_ID, AWS_SECRET_ACCESS_KEY, AWS_REGION, AWS_S3_BUCKET, FILEBROWSER_AWS_ROOT_PATH } = process.env;

// setup routes
app.use("/storage", sdk.Router([
    new sdk.LocalStorage(path.resolve(__dirname, "../examples")),
    new sdk.S3Storage(AWS_ACCESS_KEY_ID, AWS_SECRET_ACCESS_KEY, AWS_REGION, AWS_S3_BUCKET, FILEBROWSER_AWS_ROOT_PATH)
], {
    uploadPath: path.resolve(__dirname, "./upload")
}));

app.listen(process.env.PORT || 8081);